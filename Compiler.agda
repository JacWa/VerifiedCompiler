module Compiler where

  -- Data.* files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_;_≟_)
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
  ... | B | true = (bcomp a false (size B)) & B
  ... | B | false = (bcomp a false (size B z+ offset)) & B
  bcomp (x LT y)    flag offset with flag
  ... | true  = acomp x & acomp y & (JMPLESS offset :: [])
  ... | false = acomp x & acomp y & (JMPGE offset :: [])


------ Don't need absolute jump addresses. Can use offset from current position.

  compile : IExp → Prog
  compile SKIP = []
  compile (x ≔ a) = acomp a & (STORE x :: [])
  compile (this ⋯ that) = compile this & compile that
  compile (IF bool THEN this ELSE that) with compile this | compile that
  ... | THIS | THAT = (bcomp bool false (size THIS z+ + 1)) & THIS & (JMP (size THAT) :: [])  & THAT
  compile (WHILE b DO this) with compile this
  ... | body with bcomp b false (size body z+ + 1)
  ... | control = control & body & (JMP (neg (size control z+ size body z+ + 1) ) :: [])



  {-# TERMINATING #-}
  fᴴᴸ2ᴸᴸ' : IExp → ℕ × ℕ × State → ℕ × ℕ × State
  fᴴᴸ2ᴸᴸ' _        (0 , fᴸᴸ , σ)         = (0 , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' SKIP     (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' (x ≔ a) (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , suc (fᴸᴸ ℕ+ size` (acomp a)) , ((x ≔ (aexe a σ)) ∷ σ))
  fᴴᴸ2ᴸᴸ' (P ⋯ Q) (suc fᴴᴸ , fᴸᴸ , σ) = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ2ᴸᴸ' P (suc fᴴᴸ , fᴸᴸ , σ))
  fᴴᴸ2ᴸᴸ' (IF b THEN P ELSE Q) ((suc fᴴᴸ) , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' P (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (+ 1)))) , σ)
  ... | false = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (+ 1)))) , σ)
  fᴴᴸ2ᴸᴸ' (WHILE b DO c) (suc fᴴᴸ , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' (c ⋯ (WHILE b DO c)) (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ + 1))) , σ)
  ... | false = fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ + 1))) , σ

  fᴴᴸ2ᴸᴸ : IExp → ℕ → ℕ
  fᴴᴸ2ᴸᴸ I fᴴᴸ with fᴴᴸ2ᴸᴸ' I (fᴴᴸ , 0 , ⟦⟧)
  ... | fᴴᴸ' , fᴸᴸ , _ = fᴴᴸ' ℕ+ fᴸᴸ
