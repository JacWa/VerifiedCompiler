module Proofs.BigStep where

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

  BSLem1 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , suc f' ⟧ → ∃[ x ] (f ≡ suc x)
  BSLem1 Skip = _ ∣ refl
  BSLem1 Assign = _ ∣ refl
  BSLem1 (Seq sem sem₁) = _ ∣ refl
  BSLem1 (IfFalse x sem) = _ ∣ refl
  BSLem1 (IfTrue x sem) = _ ∣ refl
  BSLem1 (WhileFalse x) = _ ∣ refl
  BSLem1 (WhileTrue x sem sem₁) = _ ∣ refl

  BSLem2 : ∀ {I σ σ' f f'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → Bool
  BSLem2 Empty = false
  BSLem2 Skip = true
  BSLem2 Assign = true
  BSLem2 (Seq _ sem) = BSLem2 sem
  BSLem2 (IfFalse _ sem) = BSLem2 sem
  BSLem2 (IfTrue _ sem) = BSLem2 sem
  BSLem2 (WhileFalse _) = true
  BSLem2 (WhileTrue _ _ sem) = BSLem2 sem

  BSLem3 : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧) → BSLem2 sem ≡ true → ∃[ n ] (f ≡ suc n)
  BSLem3 Empty ()
  BSLem3 Skip prf = _ ∣ refl
  BSLem3 Assign prf = _ ∣ refl
  BSLem3 (Seq sem sem₁) prf = _ ∣ refl
  BSLem3 (IfFalse x sem) prf = _ ∣ refl
  BSLem3 (IfTrue x sem) prf = _ ∣ refl
  BSLem3 (WhileFalse x) prf = _ ∣ refl
  BSLem3 (WhileTrue x sem sem₁) prf = _ ∣ refl

  BSLem4 : ∀ {I σ σ' f f'}(sem : ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧) → BSLem2 sem ≡ false → f' ≡ 0
  BSLem4 Empty prf = refl
  BSLem4 Skip ()
  BSLem4 Assign ()
  BSLem4 (Seq sem sem₁) prf = BSLem4 sem₁ prf
  BSLem4 (IfFalse x sem) prf = BSLem4 sem prf
  BSLem4 (IfTrue x sem) prf = BSLem4 sem prf
  BSLem4 (WhileFalse x) ()
  BSLem4 (WhileTrue x sem sem₁) prf = BSLem4 sem₁ prf


  convert : ∀ {I s s' f f'} → ⟦ I , s , f ⟧↓⟦ s' , f' ⟧ → ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧
  convert Ski↓ = Skip
  convert Ass↓ = Assign
  convert (Seq↓ sem sem₁) = Seq (convert sem) (convert sem₁)
  convert (IfF↓ x sem) = IfFalse x (convert sem)
  convert (IfT↓ x sem) = IfTrue x (convert sem)
  convert (WhF↓ x) = WhileFalse x
  convert (WhT↓ x sem sem₁) = WhileTrue x (convert sem) (convert sem₁)

  BSLem5 : ∀ {I σ σ' f f'}(sem : ⟦ I , σ , f ⟧↓⟦ σ' , f' ⟧) → BSLem2 (convert sem) ≡ true
  BSLem5 Ski↓ = refl
  BSLem5 Ass↓ = refl
  BSLem5 (Seq↓ sem sem₁) = BSLem5 sem₁
  BSLem5 (IfF↓ x sem) = BSLem5 sem
  BSLem5 (IfT↓ x sem) = BSLem5 sem
  BSLem5 (WhF↓ x) = refl
  BSLem5 (WhT↓ x sem sem₁) = BSLem5 sem₁
  
  convert₂ : ∀ {I s s' f f'} → ⟦ I , s , f ⟧⇛⟦ s' , suc f' ⟧ → ⟦ I , s , f ⟧↓⟦ s' , suc f' ⟧
  convert₂ Skip = Ski↓
  convert₂ Assign = Ass↓
  convert₂ (Seq sem sem₁) with BSLem1 sem₁
  ... | f ∣ refl = Seq↓ (convert₂ sem) (convert₂ sem₁)
  convert₂ (IfFalse x sem) = IfF↓ x (convert₂ sem)
  convert₂ (IfTrue x sem) = IfT↓ x (convert₂ sem)
  convert₂ (WhileFalse x) = WhF↓ x
  convert₂ (WhileTrue x sem sem₁) with BSLem1 sem₁
  ... | f ∣ refl = WhT↓ x (convert₂ sem) (convert₂ sem₁)

  convert₃ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧) → BSLem2 sem ≡ true → ⟦ I , s , f ⟧↓⟦ s' , f' ⟧
  convert₃ Empty ()
  convert₃ Skip prf = Ski↓
  convert₃ Assign prf = Ass↓
  convert₃ (Seq sem sem₁) prf with convert₃ sem₁ prf | BSLem3 sem₁ prf
  ... | sem₁' | _ ∣ refl = Seq↓ (convert₂ sem) sem₁'
  convert₃ (IfFalse x sem) prf = IfF↓ x (convert₃ sem prf)
  convert₃ (IfTrue x sem) prf = IfT↓ x (convert₃ sem prf)
  convert₃ (WhileFalse x) prf = WhF↓ x
  convert₃ (WhileTrue x sem sem₁) prf with convert₃ sem₁ prf | BSLem3 sem₁ prf
  ... | sem₁' | _ ∣ refl = WhT↓ x (convert₂ sem) sem₁'

  revert₂ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , suc f' ⟧) → convert (convert₂ sem) ≡ sem
  revert₂ Skip = refl
  revert₂ Assign = refl
  revert₂ (Seq sem sem₁) with BSLem1 sem₁
  ... | f ∣ refl rewrite revert₂ sem | revert₂ sem₁ = refl
  revert₂ (IfFalse x sem) rewrite revert₂ sem = refl
  revert₂ (IfTrue x sem) rewrite revert₂ sem = refl
  revert₂ (WhileFalse x) = refl
  revert₂ (WhileTrue x sem sem₁) with BSLem1 sem₁
  ... | f ∣ refl rewrite revert₂ sem | revert₂ sem₁ = refl

  revert₃ : ∀ {I s s' f f'}(sem : ⟦ I , s , f ⟧⇛⟦ s' , f' ⟧)(prf : BSLem2 sem ≡ true) → convert (convert₃ sem prf) ≡ sem
  revert₃ Empty ()
  revert₃ Skip prf = refl
  revert₃ Assign prf = refl
  revert₃ (Seq sem sem₁) prf with BSLem3 sem₁ prf
  ... | _ ∣ refl rewrite revert₂ sem | revert₃ sem₁ prf = refl
  revert₃ (IfFalse x sem) prf rewrite revert₃ sem prf = refl
  revert₃ (IfTrue x sem) prf rewrite revert₃ sem prf = refl
  revert₃ (WhileFalse x) prf = refl
  revert₃ (WhileTrue x sem sem₁) prf with BSLem3 sem₁ prf
  ... | _ ∣ refl rewrite revert₂ sem | revert₃ sem₁ prf = refl
