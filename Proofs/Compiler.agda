module Proofs.Compiler where

  
  open import Data.Nat using (suc; _≤_) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_) renaming (_+_ to _ℤ+_; suc to zuc)
  open import Data.Bool using (true; false; _≟_)
  open import Data.Maybe
  open import Data.Empty
  
  open import Lang.Stack
  open import Base.DataStructures

  open import Proofs.Stack
  open import Compiler
  
  postulate
    getRest : ∀ {I I' σ s f σ' s' f' σ'' s'' f''} → 1 ≤ f'' → (compile I) ⊢⟦ config σ s (+ 0) , f ⟧⇒*⟦ config σ' s' (size (compile I)) , f' ⟧ → ((compile I) & (compile I')) ⊢⟦ config σ s (+ 0) , f ⟧⇒*⟦ config σ'' s'' (size ((compile I) & (compile I'))) , f'' ⟧ → (compile I') ⊢⟦ config σ' s' (+ 0) , f' ⟧⇒*⟦ config σ'' s'' (size (compile I')) , f'' ⟧
--  stacklem3 = {!!}
    makeSem : ∀ I {σ σ' f f'} → 1 ≤ f' → (compile I) ⊢⟦ config σ $ (+ 0) , f ⟧⇒*⟦ config σ' $ (size (compile I)) , f' ⟧
