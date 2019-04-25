module Base.Fuel where

  open import Data.Nat using (ℕ; suc) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_; ℤ) renaming (suc to zuc; _+_ to _z+_)
  open import Data.Bool using (not; Bool; false; true)
  
  open import Lang.Expr
  open import Lang.Stack
  open import Compiler
  
  open import Base.DataStructures
  
  open import Semantics.HighLevel
  open import Semantics.LowLevel


  --------------------------------------------------------
  -- Conversion of fuel from a given amount in HL to LL --
  --------------------------------------------------------


  -- Calculates the amount of fuel needed to execute a boolean expression when compiled to the low level language.
  fuelLLb : (b : BExp)(flag : Bool)(σ : Store)(offset : ℤ) → ℕ
  fuelLLb (BOOL x) flag σ z = size` (bcomp (BOOL x) flag z)
  fuelLLb (NOT b) flag σ z = fuelLLb b (not flag) σ z
  fuelLLb (b AND b') flag σ z with bexe b σ
  fuelLLb (b AND b') false σ z | false = fuelLLb b false σ (size (bcomp b' false z) z+ z)
  fuelLLb (b AND b') true σ  z | false = fuelLLb b false σ (size (bcomp b' true z))
  fuelLLb (b AND b') false σ z | true  = fuelLLb b false σ (size (bcomp b' false z) z+ z) ℕ+ fuelLLb b' false σ z
  fuelLLb (b AND b') true σ  z | true  = fuelLLb b false σ (size (bcomp b' true z))       ℕ+ fuelLLb b' true σ z
  fuelLLb (x LT y) flag σ z = size` (acomp x) ℕ+ (size` (acomp y) ℕ+ 1)

  -- Given the bigstep semantics on a high level command, this function calculates the amount of fuel needed for low level execution.
  fuelLLBS' : ∀ {I f f' σ σ'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → ℕ
  fuelLLBS' Empty = 0
  fuelLLBS' Skip = 0
  fuelLLBS' {_ ≔ a} Assign = suc (size` (acomp a))
  fuelLLBS' (Seq semhl semhl') = fuelLLBS' semhl ℕ+ fuelLLBS' semhl'
  fuelLLBS' {IF b THEN I ELSE I'} {σ = σ} (IfFalse x semhl) = fuelLLb b false σ (size (compile I) z+ + 1) ℕ+ fuelLLBS' semhl
  fuelLLBS' {IF b THEN I ELSE I'} {σ = σ} (IfTrue x semhl)  = fuelLLb b false σ (size (compile I) z+ + 1) ℕ+ fuelLLBS' semhl
  fuelLLBS' {WHILE b DO c} {σ = σ} (WhileFalse x) = fuelLLb b false σ (size (compile c) z+ + 1)
  fuelLLBS' {WHILE b DO c} {σ = σ} (WhileTrue {f' = f'} x csem semhl') with f'
  -- If fuel runs out during the exection of c, then the 1 fuel for the jump is not needed.
  ... | 0 = fuelLLb b false σ (size (compile c) z+ + 1) ℕ+ (fuelLLBS' csem ℕ+ fuelLLBS' semhl')
  ... | suc _ = fuelLLb b false σ (size (compile c) z+ + 1) ℕ+ (fuelLLBS' csem ℕ+ (1 ℕ+ fuelLLBS' semhl'))

  fuelLLBS : ∀ {f' I f σ σ'} → ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧ → ℕ
  fuelLLBS {f'} sem = fuelLLBS' sem ℕ+ f'
