module Proofs.BigStepHL where

  open import Agda.Builtin.Equality
  open import Semantics.HighLevel
  open import Data.Nat using (_≤_; s≤s; z≤n; suc)
  open import Data.Nat.Properties using (≤-refl; ≤-step; ≤-trans)

  BSLem1 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → f' ≤ f
  BSLem1 Empty = z≤n
  BSLem1 Skip = s≤s ≤-refl
  BSLem1 Assign = ≤-step ≤-refl
  BSLem1 (Seq sem sem')  = ≤-trans (BSLem1 sem') (BSLem1 sem)
  BSLem1 (IfFalse x sem) = ≤-step (BSLem1 sem)
  BSLem1 (IfTrue x sem) = ≤-step (BSLem1 sem)
  BSLem1 (WhileFalse x) = ≤-step ≤-refl
  BSLem1 (WhileTrue x sem sem') = ≤-step (≤-trans (BSLem1 sem') (BSLem1 sem))

  BSLem2 : ∀ {I σ σ' f'} → ⟦ I , σ , 0 ⟧⇛⟦ σ' , f' ⟧ → f' ≡ 0
  BSLem2 {f' = 0} sem = refl
  BSLem2 {f' = suc f} sem with BSLem1 sem
  ... | ()

  BSLem3 : ∀ {I σ σ'} → ⟦ I , σ , 0 ⟧⇛⟦ σ' , 0 ⟧ → σ' ≡ σ
  BSLem3 Empty = refl
