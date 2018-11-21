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
  bcomp (a AND b)   flag offset = {!!}
  bcomp (x LT y)    flag offset with flag
  ... | true  = acomp x & acomp y & (JMPLESS offset :: [])
  ... | false = acomp x & acomp y & (JMPGE offset :: [])


------ Don't need absolute jump addresses. Can use offset from current position.

{-
  ... | .bool = (JMP offset) :: []
  ... | _     = [] -}

  compile : IExp → Prog
  compile SKIP = []
  compile (x ≔ a) = acomp a & (STORE x :: [])
  compile (this ⋯ that) = compile this & compile that
  compile (IF bool THEN this ELSE that) with compile this
  ... | THIS = (bcomp bool false (pos (suc (len THIS)))) & THIS & compile that
  compile (WHILE b DO this) with compile this
  ... | body = (bcomp b false {!!}) & body & (JMP {!!} :: []) 
  
{-- with bool
  ... | BOOL true  = compile {n} this
  ... | BOOL false = compile {n} that
  ... | NOT _      = {!!}
  ... | x AND y    = {!!}
  ... | x LT y     = acomp x & acomp y & ( JMPLESS {!!} :: compile {len (compile {n} this) ℕ+ n} that) & compile {n} this --}
  


{--with (acomp a & acomp b [ refl ]) isEmpty?
  ... | true = []
  ... | false = ((acomp a) & (acomp b) [ refl ]) & (ADD :: []) [ refl ] --}
  
{-
  -- function: compile ETL to SML
  compile : ∀ {n} → Exp → Path n (suc n)
  compile (nat val)  = (loadi val) :: ─
  compile (var name) = (load name) :: ─
  compile (e1 + e2)  = (compile e1) >> (compile e2) >> (add :: ─)


------------------
-- Verification --
------------------

  -- proof: distributive(?) property of exs and _>>_
  >>-ex : ∀ {x y z}(env : List Var)(s : Stack x)(a : Path x y)(b : Path y z) → exs (a >> b) env s ≡ exs b env (exs a env s)
  >>-ex _ _ ─ b = refl
  >>-ex env s (a :: as) b with a | s
  ... | loadi val | ss             = >>-ex env (val                  , ss) as b
  ... | load name | ss             = >>-ex env ((get-var name env) , ss) as b
  ... | add       | (s1 , s2 , ss) = >>-ex env ((s2 ℕ+ s1)           , ss) as b
  
  -- verification of compiler
  verify : ∀ {n} (exp : Exp)(xs : Stack n)(env : List Var) → (exe exp env) , xs ≡ exs (compile exp) env xs
  verify (nat val)  _ _ = refl
  verify (var name) _ _ = refl
  verify (exp₁ + exp₂) xs env rewrite >>-ex env xs ((compile exp₁) >> (compile exp₂)) (add :: ─) | >>-ex env xs (compile exp₁) (compile exp₂) | sym (verify exp₁ xs env) | sym (verify exp₂ (exe exp₁ env , xs) env) = refl
-}
