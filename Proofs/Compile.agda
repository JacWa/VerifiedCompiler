module Proofs.Compile where

  open import Agda.Builtin.Int
  open import Agda.Builtin.Equality
  open import Data.Nat.Base

  open import Base.DataStructures
  open import Lang.Expr
  open import Lang.Stack
  open import Proofs.Expr
  open import Proofs.Stack

  open import Compiler

  open import Relation.Binary

  

  final : ∀ P {σᴴᴸ' σᴸᴸ'} → [ P , ⟦⟧ ]⇓ σᴴᴸ' → compile P ⊢ config ⟦⟧ $ (pos 0) ⇒* config σᴸᴸ' $ (size (compile P)) → σᴴᴸ' ≡ σᴸᴸ'
  final P HL LL = {!!}
