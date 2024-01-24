module Adjunction where
-- A lot of the mechanization in this file are learned from:
-- https://github.com/agda/agda-categories

open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; cong-app; sym; refl; _≢_; subst; module ≡-Reasoning) public

Arrow : Set₁ → Set₁ → Set₁
Arrow A B = A → B → Set

-- This isn't the best definition of Categories.
-- But hopefully it'll do the job :)
record Category : Set₂ where
  infixr 9 _∘_
  field
    -- Objects
    Object : Set₁
    -- Maps
    _⇒_ : Arrow Object Object
    -- Identity Maps
    id : ∀ {A : Object} → A ⇒ A
    -- Composite Maps
    _∘_ : ∀ {A B C : Object} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    -- identity laws
    idᵣ : ∀ {A B : Object} → (f : A ⇒ B) → f ∘ id ≡ f
    idₗ : ∀ {A B : Object} → (f : A ⇒ B) → id ∘ f ≡ f
    -- associative law
    assoc : ∀ {A B C D : Object} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D)
                → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

_[_,_] : (C : Category) → Category.Object C → Category.Object C → Set
C [ a , b ] = a ⇒ b
  where open Category C

_[_∘_] : (C : Category) → {a b c : Category.Object C} → (g : C [ b , c ]) → (f : C [ a , b ]) → C [ a , c ]
C [ g ∘ f ] = g ∘ f
  where open Category C

record isomorphism (C : Category) (a b : Category.Object C) : Set where
  open Category C
  field
    to : (a ⇒ b)
    from : (b ⇒ a)
    id₁ : from ∘ to ≡ id
    id₂ : to ∘ from ≡ id

record Functor (C D : Category) : Set₁ where
  private module C = Category C
  private module D = Category D
  field
    F₀ : C.Object → D.Object
    F₁ : ∀ {a b : C.Object} → C [ a , b ] → D [ F₀ a , F₀ b ]
    identity : ∀ {a : C.Object} → F₁ (C.id {a}) ≡ D.id
    comp : ∀ {a b c : C.Object} {f : C [ a , b ]} {g : C [ b , c ]} → F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ]
  ₀ = F₀
  ₁ = F₁

Endofunctor : Category → Set₁
Endofunctor C = Functor C C

variable
  C D : Category
  L : Functor C D
  R : Functor D C

record Adjunction {C D : Category} (L : Functor C D) (R : Functor D C) : Set₁ where
  module C = Category C
  module D = Category D
  module L = Functor L
  module R = Functor R
  field
    Adjₗ : ∀ {a : C.Object} {b : D.Object} → C [ a , R.₀ b ] ≡ D [ L.₀ a , b ]

-- Natural Transformations
-- Somehow when I was formalizing this, I was once again confused about "naturality".
-- Then I found the post below quite satisfying:
-- https://math.stackexchange.com/questions/2660049/intuitive-meaning-of-naturality
record NaturalTrans (F G : Functor C D): Set₁ where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  open D using (_∘_)
  field
    η : ∀ (X : C.Object) → D [ F.F₀ X , G.F₀ X ]
    commute : ∀ {X Y : C.Object} → (f : C [ X , Y ]) → η Y ∘ F.F₁ f ≡ G.F₁ f ∘ η X
    -- agda-categories does this
    sym-commute : ∀ {X Y : C.Object} → (f : C [ X , Y ]) → G.F₁ f ∘ η X ≡ η Y ∘ F.F₁ f

-- From wiki
-- A monad on C consists of an endofunctor T : C → C together with two natural transformations:
-- η : 1c → T (where 1c denotes the identity functor on C) and
-- μ : T² → T (where T² is the functor T ∘ T : C → C)
-- These are required to fulfill the following two laws:
-- μ ∘ Tμ ≡ μ ∘ μT
-- μ ∘ Tη ≡ μ ∘ ηT ≡ 1T
record Monad (T : Endofunctor C) : Set₁ where
  module C = Category C
  field
    -- η : (∀ {a : C.Object} → C [ a , a ]) → T
