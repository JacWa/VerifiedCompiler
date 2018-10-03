module Proofs.NumProofs where

  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality

  _-_ : ℕ → ℕ → ℤ
  0 - 0             = pos 0
  0 - (suc n)       = negsuc n
  m - 0             = pos m
  (suc m) - (suc n) = m - n

  
