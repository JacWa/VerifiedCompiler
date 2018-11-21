module Compiler where

  -- Data.* files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Misc.Base
  open import Base.DataStructures
  open import Lang.Expr
  open import Lang.Stack
  open import Relation.Nullary

--------------
-- Compiler --
--------------

  acomp : AExp → Prog
  acomp (NAT n) = (LOADI n) :: []
  acomp (VAR v) = (LOAD v) :: []
  acomp (a + b) = acomp a & acomp b & ADD :: []

  bcomp : BExp → (flag : Bool) → (offset : ℤ) → Prog
  bcomp (BOOL bool) flag offset with flag ≟ bool
  ... | yes p = (JMP offset) :: []
  ... | no _  = []
  bcomp (NOT bool)  flag offset = bcomp bool (not flag) offset
  bcomp (a AND b)   flag offset with bcomp b flag offset | flag
  ... | B | true = (bcomp a false (pos (len B))) & B
  ... | B | false = (bcomp a false (pos (len B) z+ offset)) & B
  bcomp (x LT y)    flag offset with flag
  ... | true  = acomp x & acomp y & (JMPLESS offset :: [])
  ... | false = acomp x & acomp y & (JMPGE offset :: [])


------ Don't need absolute jump addresses. Can use offset from current position.

  compile : IExp → Prog
  compile SKIP = []
  compile (x ≔ a) = acomp a & (STORE x :: [])
  compile (this ⋯ that) = compile this & compile that
  compile (IF bool THEN this ELSE that) with compile this | compile that
  ... | THIS | THAT = (bcomp bool false (pos (suc (len THIS)))) & THIS & (JMP (pos (len THAT)) :: [])  & THAT
  compile (WHILE b DO this) with compile this
  ... | body with bcomp b false ((pos ((len body) ℕ+ 1)))
  ... | control = control & body & (JMP (negsuc ((len control) ℕ+ (len body))) :: [])
