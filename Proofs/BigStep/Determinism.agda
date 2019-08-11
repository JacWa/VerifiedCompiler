module Proofs.BigStep.Determinism where
  
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
  open import Data.Empty

  mutual
    det-σ : ∀ {I σ σ' σ* f f' f*} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → ⟦ I , σ , f ⟧⇛⟦ σ* , f* ⟧ → σ' ≡ σ*
    det-σ Empty Empty = refl
    det-σ Skip Skip = refl
    det-σ Assign Assign = refl
    det-σ (Seq sem1 sem3) (Seq sem2 sem4) with det-σ sem1 sem2 | det-f sem1 sem2
    ... | σ-p1 | f-p1 rewrite σ-p1 | f-p1 = det-σ sem3 sem4
    det-σ (IfFalse x sem1) (IfFalse x' sem2) = det-σ sem1 sem2
    det-σ (IfFalse x sem1) (IfTrue ¬x sem2) rewrite x with ¬x
    ... | ()
    det-σ (IfTrue x sem1) (IfFalse ¬x sem2) rewrite x with ¬x
    ... | ()
    det-σ (IfTrue x sem1) (IfTrue x' sem2) = det-σ sem1 sem2
    det-σ (WhileFalse x) (WhileFalse x₁) = refl
    det-σ (WhileFalse x) (WhileTrue ¬x sem2 sem3) rewrite x with ¬x
    ... | ()
    det-σ (WhileTrue x sem1 sem3) (WhileFalse ¬x) rewrite x with ¬x
    ... | ()
    det-σ (WhileTrue x sem1 sem3) (WhileTrue x' sem2 sem4) with det-σ sem1 sem2 | det-f sem1 sem2
    ... | σ-p1 | f-p1 rewrite σ-p1 | f-p1 = det-σ sem3 sem4

    det-f : ∀ {I σ σ' σ* f f' f*} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → ⟦ I , σ , f ⟧⇛⟦ σ* , f* ⟧ → f' ≡ f*
    det-f Empty Empty = refl
    det-f Skip Skip = refl
    det-f Assign Assign = refl
    det-f (Seq sem1 sem3) (Seq sem2 sem4) with det-σ sem1 sem2 | det-f sem1 sem2
    ... | σ-p1 | f-p1 rewrite σ-p1 | f-p1 = det-f sem3 sem4
    det-f (IfFalse x sem1) (IfFalse x' sem2) = det-f sem1 sem2
    det-f (IfFalse x sem1) (IfTrue ¬x sem2) rewrite x with ¬x
    ... | ()
    det-f (IfTrue x sem1) (IfFalse ¬x sem2) rewrite x with ¬x
    ... | ()
    det-f (IfTrue x sem1) (IfTrue x' sem2) = det-f sem1 sem2
    det-f (WhileFalse x) (WhileFalse x₁) = refl
    det-f (WhileFalse x) (WhileTrue ¬x sem2 sem3) rewrite x with ¬x
    ... | ()
    det-f (WhileTrue x sem1 sem3) (WhileFalse ¬x) rewrite x with ¬x
    ... | ()
    det-f (WhileTrue x sem1 sem3) (WhileTrue x' sem2 sem4) with det-σ sem1 sem2 | det-f sem1 sem2
    ... | σ-p1 | f-p1 rewrite σ-p1 | f-p1 = det-f sem3 sem4
