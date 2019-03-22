module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Basic
  open import Proofs.Stack
  open import Proofs.Expr
  open import Proofs.NatProofs
  open import Misc.Base
  open import Base.DataStructures renaming (State to Store)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Bool.Base
  open import Relation.Nullary

  data StateHL : Set where
    statehl : Store → (fuel : ℕ) → StateHL

  getHLσ : StateHL → Store
  getHLσ (statehl σ _) = σ

  data _⊗_ (A B : Set) : Set where
    _∪_ : (a : A)(b : B) → A ⊗ B



  storeHL' : IExp → StateHL → StateHL
  storeHL' i (statehl σ 0)                          = statehl σ 0
  storeHL' SKIP                 (statehl σ (suc f)) = statehl σ f
  storeHL' (x ≔ a)               (statehl σ (suc f)) = statehl ((x ≔ aexe a σ) ∷ σ) f
  storeHL' (P ⋯ Q)               (statehl σ (suc f)) = storeHL' Q (storeHL' P (statehl σ f))
  storeHL' (IF b THEN P ELSE Q) (statehl σ (suc f)) with bexe b σ
  ... | true  = storeHL' P (statehl σ f)
  ... | false = storeHL' Q (statehl σ f)
  storeHL' (WHILE b DO c)       (statehl σ (suc f)) with bexe b σ
  ... | true  = storeHL' (WHILE b DO c) (statehl σ f)
  ... | false = statehl σ f

{-
  storeHL : IExp → ℕ → Store
  storeHL i f = getHLσ (storeHL' i (statehl ⟦⟧ f))
  -}
