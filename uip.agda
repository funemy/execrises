{-- ice1000 has a relevant blog: https://ice1000.org/2020/08-15-AxiomK.html --}
module UIP where

open import Agda.Primitive

module HeteroEq where
  private
    variable
      ℓa ℓb : Level

  data _≡_ {A : Set ℓa} (a : A) : {B : Set ℓb} → B -> Set ℓa where
    refl : a ≡ a

  J : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
      → (target : a ≡ b)
      → (motive : {ℓx : Level} → {X : Set ℓx} → {x : X} → a ≡ x → Set ℓa)
      → (base : motive refl)
      → motive target
  J refl motive base = base

  uip' : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
         → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip' refl refl = refl

  uip : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
        → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip g h = J h (λ a≡x → g ≡ a≡x) (J g (λ a≡x → a≡x ≡ refl) refl)

module HomoEq where
  private
    variable
      ℓ : Level

  data _≡_ {A : Set ℓ} (a : A) : A -> Set ℓ where
    refl : a ≡ a

  J : {A : Set ℓ} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : {x : A} → a ≡ x → Set ℓ)
      → (base : motive refl)
      → motive target
  J refl motive base = base

  -- You can still prove uip of homogeneous ≡ using dependent pattern matching
  uip' : {A : Set ℓ} → {a : A} → {b : A}
         → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip' refl refl = refl

  uip : {A : Set ℓ} → {a : A} → {b : A}
        → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  -- we cannot put `g ≡ a≡x` in the first hole anymore
  uip g h = J h (λ a≡x → {!!}) {!!}

