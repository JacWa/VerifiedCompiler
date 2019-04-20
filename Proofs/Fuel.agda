module Proofs.Fuel where

  open import Data.Nat using (ℕ; suc) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_; ℤ) renaming (suc to zuc; _+_ to _z+_)
  open import Data.Bool using (not; Bool; false; true)
  open import Agda.Builtin.Equality
  open import Lang.Expr
  open import Lang.Stack
  open import Proofs.Expr
  open import Compiler
  open import Base.DataStructures
  open import Semantics.HighLevel
  
  

  fuelLLb : (b : BExp)(flag : Bool)(σ : State)(offset : ℤ) → ℕ
  fuelLLb (BOOL x) flag σ z = size` (bcomp (BOOL x) flag z)
  fuelLLb (NOT b) flag σ z = fuelLLb b (not flag) σ z
  fuelLLb (b AND b') flag σ z with bexe b σ
  fuelLLb (b AND b') false σ z | false = fuelLLb b false σ (size (bcomp b' false z) z+ z)
  fuelLLb (b AND b') true σ  z | false = fuelLLb b false σ (size (bcomp b' true z))
  fuelLLb (b AND b') false σ z | true  = fuelLLb b false σ (size (bcomp b' false z) z+ z) ℕ+ fuelLLb b' false σ z
  fuelLLb (b AND b') true σ  z | true  = fuelLLb b false σ (size (bcomp b' true z))       ℕ+ fuelLLb b' true σ z
  fuelLLb (x LT y) flag σ z = size` (acomp x) ℕ+ (size` (acomp y) ℕ+ 1)
 
  fuelLL' : ∀ P {f σ σ' Q f'} → ⟦ σ , P , suc f ⟧↦⟦ σ' , Q , f' ⟧ → ℕ
  fuelLL' SKIP ()
  fuelLL' (x ≔ a) _ = suc (size` (acomp a))
  fuelLL' (SKIP ⋯ Q) _ = 0
  fuelLL' (P ⋯ Q) (seqstep y) = fuelLL' P y
  fuelLL' (IF b THEN P ELSE Q) {σ = σ} _ = fuelLLb b false σ (size (compile P) z+ + 1)
  fuelLL' (WHILE b DO c) {σ = σ} _ = fuelLLb b false σ (size (compile c) z+ + 1)

  fuelLL : ∀ I f {f' σ σ'} → ⟦ σ , I , f ⟧↦*⟦ σ' , SKIP , f' ⟧ → ℕ
  fuelLL _ 0 _ = 0
  fuelLL I (suc f) done = suc f
  fuelLL I (suc f) (step {I' = I'} {f'} one rest) = fuelLL' I one ℕ+ fuelLL I' f'  rest

  fuelSKIP : ∀ f {f' σ σ'} → {rest : ⟦ σ , SKIP , f ⟧↦*⟦ σ' , SKIP , f' ⟧} → fuelLL SKIP f rest ≡ f
  fuelSKIP 0 = refl
  fuelSKIP (suc f) {rest = done} = refl
  fuelSKIP (suc f) {rest = step () _}
