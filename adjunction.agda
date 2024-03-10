module Adjunction where
-- A lot of the mechanization in this file are learned from:
-- https://github.com/agda/agda-categories

open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; cong-app; sym; refl; _≢_; subst; module ≡-Reasoning) public

Arrow : Set → Set → Set₁
Arrow A B = A → B → Set

-- This isn't the best definition of Categories.
-- But hopefully it'll do the job :)
record Category : Set₁ where
  infixr 9 _∘_
  field
    -- Objects
    Object : Set
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

∘-comm : {C : Category} → {a b c d : Category.Object C}
       → {f : C [ a , b ]} → {g : C [ b , c ]} → {h : C [ c , d ]}
       → C [ h ∘ C [ g ∘ f ] ] ≡ C [ C [ h ∘ g ] ∘ f ]
∘-comm {C = C} {f = f} {g = g} {h = h} = Category.assoc C f g h

∘-congᵣ : {C : Category} → {a b c : Category.Object C}
        → {g h : C [ b , c ]}
        → (f : C [ a , b ])
        → g ≡ h
        → let _∘_ = Category._∘_ C in (g ∘ f ≡ h ∘ f)
∘-congᵣ f refl = refl

∘-congₗ : {C : Category} → {a b c : Category.Object C}
        → {g h : C [ a , b ]}
        → (f : C [ b , c ])
        → g ≡ h
        → let _∘_ = Category._∘_ C in (f ∘ g ≡ f ∘ h)
∘-congₗ f refl = refl

record isomorphism (C : Category) (a b : Category.Object C) : Set where
  open Category C
  field
    to : (a ⇒ b)
    from : (b ⇒ a)
    id₁ : from ∘ to ≡ id
    id₂ : to ∘ from ≡ id

record Functor (C D : Category) : Set where
  private module C = Category C
  private module D = Category D
  field
    F₀ : C.Object → D.Object
    F₁ : ∀ {a b : C.Object} → C [ a , b ] → D [ F₀ a , F₀ b ]
    identity : ∀ {a : C.Object} → F₁ (C.id {a}) ≡ D.id
    comp : ∀ {a b c : C.Object} {f : C [ a , b ]} {g : C [ b , c ]} → F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ]

Endofunctor : Category → Set
Endofunctor C = Functor C C

-- identity Functor
idF : ∀ {C : Category} → Endofunctor C
Functor.F₀ idF = λ x → x
Functor.F₁ idF = λ f → f
Functor.identity idF = refl
Functor.comp idF = refl

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
    Adjₗ : ∀ {a : C.Object} {b : D.Object} → C [ a , R.F₀ b ] ≡ D [ L.F₀ a , b ]

-- Natural Transformations
-- Somehow when I was formalizing this, I was once again confused about "naturality".
-- Then I found the post below quite satisfying:
-- https://math.stackexchange.com/questions/2660049/intuitive-meaning-of-naturality
record NaturalTrans (F G : Functor C D): Set where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  open D using (_∘_)
  field
    η : ∀ (X : C.Object) → D [ F.F₀ X , G.F₀ X ]
    -- naturality
    commute : ∀ {X Y : C.Object} → (f : C [ X , Y ]) → η Y ∘ F.F₁ f ≡ G.F₁ f ∘ η X
    -- agda-categories has this
    sym-commute : ∀ {X Y : C.Object} → (f : C [ X , Y ]) → G.F₁ f ∘ η X ≡ η Y ∘ F.F₁ f

-- Identity Natural Transformation
idN : {F : Functor C D} → NaturalTrans F F
NaturalTrans.η (idN {_} {D}) X = D.id
  where module D = Category D
NaturalTrans.commute (idN {_} {D} {F}) f =
  let step1 = D.idᵣ (F.F₁ f)
      step2 = D.idₗ (F.F₁ f)
  in trans step2 (sym step1)
    where
    module D = Category D
    module F = Functor F
NaturalTrans.sym-commute (idN {_} {D} {F}) f =
  let step1 = D.idᵣ (F.F₁ f)
      step2 = D.idₗ (F.F₁ f)
  in trans step1 (sym step2)
    where
    module D = Category D
    module F = Functor F

-- Compoistion of Natural Transformations
Nat∘ : {F G H : Functor C D} → NaturalTrans G H → NaturalTrans F G → NaturalTrans F H
NaturalTrans.η (Nat∘ {D = D} Nat[G,H] Nat[F,G]) X =
  let ηGH = NaturalTrans.η Nat[G,H] X
      ηFG = NaturalTrans.η Nat[F,G] X
  in D [ ηGH ∘ ηFG ]
  where module D = Category D
NaturalTrans.commute (Nat∘ {C} {D} Nat[G,H] Nat[F,G]) {X} {Y} f =
  let step1 = commute Nat[G,H] f
      step2 = commute Nat[F,G] f
      D[X,X'] = η Nat[F,G] X
      step3 = ∘-congᵣ {C = D} D[X,X'] step1
      D[Y',Y''] = η Nat[G,H] Y
      step4 = ∘-congₗ {C = D} D[Y',Y''] step2
      step5 = trans step4 (trans (∘-comm {C = D}) step3)
  in trans (sym (∘-comm {C = D})) (trans step5 (sym (∘-comm {C = D})))
  where
    open NaturalTrans
    open Category
    open Category D

NaturalTrans.sym-commute (Nat∘ Nat[G,H] Nat[F,G]) f = {!!}

idN-cancelᵣ : {A B : Functor C D} → (F : NaturalTrans A B) → Nat∘ F idN ≡ F
idN-cancelᵣ F = let step1 = Nat∘ F idN in {!!}

idN-cancelₗ : {A B : Functor C D} → (F : NaturalTrans A B) → Nat∘ idN F ≡ F
idN-cancelₗ F = {!!}


-- Functor Category
Fun : (C : Category) → (D : Category) → Category
-- object
Category.Object (Fun C D) = Functor C D
-- morphism
Category._⇒_ (Fun C D) = λ F G → NaturalTrans F G
-- id
Category.id (Fun C D) = idN
-- compose
Category._∘_ (Fun C D) Nat[B,C] Nat[A,B] = Nat∘ Nat[B,C] Nat[A,B]
-- id law
Category.idᵣ (Fun C D) F = {!!}
Category.idₗ (Fun C D) F = {!!}
-- assoc law
Category.assoc (Fun C D) F G H = {!!}
   -- where
   --  open Category
   --  private module C = Category C
   --  private module D = Category D

-- From wiki
-- A monad on C consists of an endofunctor T : C → C together with two natural transformations:
-- η : 1c → T (where 1c denotes the identity functor on C) and
-- μ : T² → T (where T² is the functor T ∘ T : C → C)
-- These are required to fulfill the following two laws:
-- μ ∘ Tμ ≡ μ ∘ μT
-- μ ∘ Tη ≡ μ ∘ ηT ≡ 1T
-- TODO
-- record Monad (T : Endofunctor C) : Set₁ where
--   module C = Category C
--   field
    -- η : (∀ {a : C.Object} → C [ a , a ]) → T

