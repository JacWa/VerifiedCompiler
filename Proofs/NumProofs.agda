module Proofs.NumProofs where

  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool

  _-_ : ℕ → ℕ → ℤ
  0 - 0             = pos 0
  0 - (suc n)       = negsuc n
  m - 0             = pos m
  (suc m) - (suc n) = m - n

  ℕ=? : ℕ → ℕ → Bool
  ℕ=? 0       0       = true
  ℕ=? (suc n) (suc m) = ℕ=? n m
  ℕ=? _       _       = false

  ℤ=? : ℤ → ℤ → Bool
  ℤ=? (pos a)    (pos b)    = ℕ=? a b
  ℤ=? (negsuc a) (negsuc b) = ℕ=? a b
  ℤ=? _          _          = false

 

{--  ℤ=? : ℤ → ℤ → Bool
  ℤ=? (pos a)    (pos b)    = ℕ=? a b
  ℤ=? (negsuc a) (negsuc b) = ℕ=? a b
  ℤ=? _          _          = false
--}
  
  
