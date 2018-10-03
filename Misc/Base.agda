module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Bool

  private
    data _≤_ : ℕ → ℕ → Set where
      z≤x  : ∀ {n} → 0 ≤ n
      ≤suc : ∀ {n m} → n ≤ m → (suc n) ≤ (suc m)

  is_≤_ : ℕ → ℕ → Bool
  is 0 ≤ x             = true
  is (suc y) ≤ 0       = false
  is (suc y) ≤ (suc x) = is y ≤ x

  infixr 20 _×_ _ω_
  data _ω_ {A B : Set} : Set → Set → Set where
    _×_ : (a : A)(b : B) → A ω B

  ∣_∣ : ℤ → ℕ
  ∣ pos x ∣ = x
  ∣ negsuc x ∣ = suc x
  
