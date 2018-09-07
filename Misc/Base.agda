module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
   
  data _≤_ : ℕ → ℕ → Set where
    equals   : ∀ {n} → n ≤ n
    lessthan : ∀ {n m} → n ≤ m → n ≤ (suc m)

  infixr 20 _×_ _ω_
  data _ω_ {A B : Set} : Set → Set → Set where
    _×_ : (a : A)(b : B) → A ω B
