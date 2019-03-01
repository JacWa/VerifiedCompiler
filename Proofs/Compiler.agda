module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Basic
  open import Proofs.Stack
  open import Proofs.Expr
  open import Proofs.NatProofs
  open import Misc.Base
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Bool.Base
  open import Relation.Nullary

  
