module Proofs.Fuel where

  open import Data.Nat renaming (_+_ to _ℕ+_)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_)
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality

  open import Lang.Expr
  open import Lang.Stack
  open import Proofs.Expr
  open import Compiler
  

--  fuelLLb : (b : BExp)(σ : State) → ℕ
 
  fuelLL' : ∀ P {f σ σ' Q f'} → ⟦ σ , P , suc f ⟧↦⟦ σ' , Q , f' ⟧ → ℕ
  fuelLL' SKIP ()
  fuelLL' (x ≔ a) _ = suc (size` (acomp a))
  fuelLL' (SKIP ⋯ Q) _ = 0
  fuelLL' (P ⋯ Q) (seqstep y) = fuelLL' P y
  fuelLL' (IF b THEN P ELSE Q) _ = size` (bcomp b false (size (compile P) z+ + 1))
  fuelLL' (WHILE b DO c) _ = size` (bcomp b false (size (compile c) z+ + 1))

  fuelLL : ∀ I f {f' σ σ'} → ⟦ σ , I , f ⟧↦*⟦ σ' , SKIP , f' ⟧ → ℕ
  fuelLL _ 0 _ = 0
  fuelLL I (suc f) done = suc f
  fuelLL I (suc f) (step {I' = I'} {f'} one rest) = fuelLL' I one ℕ+ fuelLL I' f'  rest

  fuelSKIP : ∀ f {f' σ σ'} → {rest : ⟦ σ , SKIP , f ⟧↦*⟦ σ' , SKIP , f' ⟧} → fuelLL SKIP f rest ≡ f
  fuelSKIP 0 = refl
  fuelSKIP (suc f) {rest = done} = refl
  fuelSKIP (suc f) {rest = step () _}
