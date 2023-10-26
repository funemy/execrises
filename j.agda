open import Agda.Primitive

module J where
  private
    variable
      ℓ : Level

  data _≡_ {A : Set ℓ} (a : A) : A -> Set ℓ where
    refl : a ≡ a

  -- This is called based path induction
  J-based : {A : Set ℓ} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x : A) → a ≡ x → Set ℓ)
      → (base : motive a refl)
      → motive b target
  J-based refl motive base = base

  -- This is the J (or path induction) rule defined by Martin-Löf
  J : {A : Set ℓ} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x y : A) → x ≡ y → Set ℓ)
      → (base : (z : A) → motive z z refl)
      → motive a b target
  J {_} {_} {a} {b} refl motive base = base a

  JBasedSort : Setω
  JBasedSort = {ℓj : Level} → {A : Set ℓj} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x : A) → a ≡ x → Set ℓj)
      → (base : motive a refl)
      → motive b target


  JSort : Setω
  JSort = {ℓj : Level} → {A : Set ℓj} → {a : A} → {b : A}
         → (target : a ≡ b)
         → (motive : (x y : A) → x ≡ y → Set ℓj)
         → (base : (z : A) → motive z z refl)
         → motive a b target


  -- Can we prove the two J rule definitions are equivalent?
  JB⇒J : JBasedSort → JSort
  JB⇒J JB {_} {_} {a} {_} = λ target motive base → JB target (motive a) (base a)

  -- we should also be able to define this?
  J⇒JB : JSort → JBasedSort
  J⇒JB = {!!}
