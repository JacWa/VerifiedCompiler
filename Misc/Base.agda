module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
   
  data _≤_ : ℕ → ℕ → Set where
    equals   : ∀ {n} → n ≤ n
    lessthan : ∀ {n m} → n ≤ m → n ≤ (suc m)
