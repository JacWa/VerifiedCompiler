module Proofs.BigStep.Base where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Sigma renaming (_,_ to _∣_)
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Bool
  open import Base.Existential
  open import Base.DataStructures
  open import Semantics.HighLevel
  open import Data.Nat using (_≤_; s≤s; z≤n; suc)
  open import Data.Nat.Properties using (≤-refl; ≤-step; ≤-trans)
  open import Lang.Expr
  open import Relation.Nullary

  ------------------------------------------------
  -- Proofs about high level big-step semantics --
  ------------------------------------------------

  -- Fuel can never increase over execution.
  BSLem1 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → f' ≤ f
  BSLem1 Empty = z≤n
  BSLem1 Skip = s≤s ≤-refl
  BSLem1 Assign = ≤-step ≤-refl
  BSLem1 (Seq sem sem')  = ≤-trans (BSLem1 sem') (BSLem1 sem)
  BSLem1 (IfFalse x sem) = ≤-step (BSLem1 sem)
  BSLem1 (IfTrue x sem) = ≤-step (BSLem1 sem)
  BSLem1 (WhileFalse x) = ≤-step ≤-refl
  BSLem1 (WhileTrue x sem sem') = ≤-step (≤-trans (BSLem1 sem') (BSLem1 sem))

  BSLem2 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , suc f' ⟧ → ∃[ x ] (f ≡ suc x)
  BSLem2 Skip = _ ∣ refl
  BSLem2 Assign = _ ∣ refl
  BSLem2 (Seq sem sem₁) = _ ∣ refl
  BSLem2 (IfFalse x sem) = _ ∣ refl
  BSLem2 (IfTrue x sem) = _ ∣ refl
  BSLem2 (WhileFalse x) = _ ∣ refl
  BSLem2 (WhileTrue x sem sem₁) = _ ∣ refl

  BSLem3 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → Bool
  BSLem3 Empty = false
  BSLem3 Skip = true
  BSLem3 Assign = true
  BSLem3 (Seq _ sem) = BSLem3 sem
  BSLem3 (IfFalse _ sem) = BSLem3 sem
  BSLem3 (IfTrue _ sem) = BSLem3 sem
  BSLem3 (WhileFalse _) = true
  BSLem3 (WhileTrue _ _ sem) = BSLem3 sem

  BSLem4 : ∀ {I σ σ' f f'} → (sem : ⟦ I , σ , f ⟧⇛⟦ σ' , suc f' ⟧) → BSLem3 sem ≡ true
  BSLem4 Skip = refl
  BSLem4 Assign = refl
  BSLem4 (Seq sem sem₁) = BSLem4 sem₁
  BSLem4 (IfFalse x sem) = BSLem4 sem
  BSLem4 (IfTrue x sem) = BSLem4 sem
  BSLem4 (WhileFalse x) = refl
  BSLem4 (WhileTrue x sem sem₁) = BSLem4 sem₁

  BSLem5 : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧) → BSLem3 sem ≡ true → ∃[ n ] (f ≡ suc n)
  BSLem5 Empty ()
  BSLem5 Skip prf = _ ∣ refl
  BSLem5 Assign prf = _ ∣ refl
  BSLem5 (Seq sem sem₁) prf = _ ∣ refl
  BSLem5 (IfFalse x sem) prf = _ ∣ refl
  BSLem5 (IfTrue x sem) prf = _ ∣ refl
  BSLem5 (WhileFalse x) prf = _ ∣ refl
  BSLem5 (WhileTrue x sem sem₁) prf = _ ∣ refl

  BSLem6 : ∀ {I σ σ' f f'}(sem : ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧) → BSLem3 sem ≡ false → f' ≡ 0
  BSLem6 Empty prf = refl
  BSLem6 Skip ()
  BSLem6 Assign ()
  BSLem6 (Seq sem sem₁) prf = BSLem6 sem₁ prf
  BSLem6 (IfFalse x sem) prf = BSLem6 sem prf
  BSLem6 (IfTrue x sem) prf = BSLem6 sem prf
  BSLem6 (WhileFalse x) ()
  BSLem6 (WhileTrue x sem sem₁) prf = BSLem6 sem₁ prf


  convert : ∀ {I s s' f f'} → ⟦ I , s , f ⟧↓⟦ s' , f' ⟧ → ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧
  convert Ski↓ = Skip
  convert Ass↓ = Assign
  convert (Seq↓ sem sem₁) = Seq (convert sem) (convert sem₁)
  convert (IfF↓ x sem) = IfFalse x (convert sem)
  convert (IfT↓ x sem) = IfTrue x (convert sem)
  convert (WhF↓ x) = WhileFalse x
  convert (WhT↓ x sem sem₁) = WhileTrue x (convert sem) (convert sem₁)

  BSLem7 : ∀ {I σ σ' f f'}(sem : ⟦ I , σ , f ⟧↓⟦ σ' , f' ⟧) → BSLem3 (convert sem) ≡ true
  BSLem7 Ski↓ = refl
  BSLem7 Ass↓ = refl
  BSLem7 (Seq↓ sem sem₁) = BSLem7 sem₁
  BSLem7 (IfF↓ x sem) = BSLem7 sem
  BSLem7 (IfT↓ x sem) = BSLem7 sem
  BSLem7 (WhF↓ x) = refl
  BSLem7 (WhT↓ x sem sem₁) = BSLem7 sem₁
  
  convert₂ : ∀ {I s s' f f'} → ⟦ I , s , f ⟧⇛⟦ s' , suc f' ⟧ → ⟦ I , s , f ⟧↓⟦ s' , suc f' ⟧
  convert₂ Skip = Ski↓
  convert₂ Assign = Ass↓
  convert₂ (Seq sem sem₁) with BSLem2 sem₁
  ... | f ∣ refl = Seq↓ (convert₂ sem) (convert₂ sem₁)
  convert₂ (IfFalse x sem) = IfF↓ x (convert₂ sem)
  convert₂ (IfTrue x sem) = IfT↓ x (convert₂ sem)
  convert₂ (WhileFalse x) = WhF↓ x
  convert₂ (WhileTrue x sem sem₁) with BSLem2 sem₁
  ... | f ∣ refl = WhT↓ x (convert₂ sem) (convert₂ sem₁)

  convert₃ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧) → BSLem3 sem ≡ true → ⟦ I , s , f ⟧↓⟦ s' , f' ⟧
  convert₃ Empty ()
  convert₃ Skip prf = Ski↓
  convert₃ Assign prf = Ass↓
  convert₃ (Seq sem sem₁) prf with convert₃ sem₁ prf | BSLem5 sem₁ prf
  ... | sem₁' | _ ∣ refl = Seq↓ (convert₂ sem) sem₁'
  convert₃ (IfFalse x sem) prf = IfF↓ x (convert₃ sem prf)
  convert₃ (IfTrue x sem) prf = IfT↓ x (convert₃ sem prf)
  convert₃ (WhileFalse x) prf = WhF↓ x
  convert₃ (WhileTrue x sem sem₁) prf with convert₃ sem₁ prf | BSLem5 sem₁ prf
  ... | sem₁' | _ ∣ refl = WhT↓ x (convert₂ sem) sem₁'

  revert₂ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , suc f' ⟧) → convert (convert₂ sem) ≡ sem
  revert₂ Skip = refl
  revert₂ Assign = refl
  revert₂ (Seq sem sem₁) with BSLem2 sem₁
  ... | f ∣ refl rewrite revert₂ sem | revert₂ sem₁ = refl
  revert₂ (IfFalse x sem) rewrite revert₂ sem = refl
  revert₂ (IfTrue x sem) rewrite revert₂ sem = refl
  revert₂ (WhileFalse x) = refl
  revert₂ (WhileTrue x sem sem₁) with BSLem2 sem₁
  ... | f ∣ refl rewrite revert₂ sem | revert₂ sem₁ = refl

  revert₃ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧)(prf : BSLem3 sem ≡ true) → convert (convert₃ sem prf) ≡ sem
  revert₃ Empty ()
  revert₃ Skip prf = refl
  revert₃ Assign prf = refl
  revert₃ (Seq sem sem₁) prf with BSLem5 sem₁ prf
  ... | _ ∣ refl rewrite revert₂ sem | revert₃ sem₁ prf = refl
  revert₃ (IfFalse x sem) prf rewrite revert₃ sem prf = refl
  revert₃ (IfTrue x sem) prf rewrite revert₃ sem prf = refl
  revert₃ (WhileFalse x) prf = refl
  revert₃ (WhileTrue x sem sem₁) prf with BSLem5 sem₁ prf
  ... | _ ∣ refl rewrite revert₂ sem | revert₃ sem₁ prf = refl
