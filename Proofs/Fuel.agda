module Proofs.Fuel where

  open import Data.Nat using (ℕ; suc) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_; ℤ) renaming (suc to zuc; _+_ to _z+_)
  open import Data.Bool using (not; Bool; false; true)
  open import Agda.Builtin.Equality
  open import Lang.Expr
  open import Lang.Stack
  open import Proofs.Basic
  open import Proofs.Expr
  open import Proofs.ArithSemantics
  open import Proofs.NatProofs
  open import Compiler
  open import Base.DataStructures
  open import Base.Existential
  open import Base.Tuple renaming (_,_ to _~_)
  open import Agda.Builtin.Sigma using () renaming (_,_ to _∣_)
  open import Semantics.HighLevel
  open import Semantics.LowLevel
  open import Data.Empty
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality.Core using (subst)
  
  

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

  seqstp≡ : ∀ {that x σ f σ' this'} → (hlstep : ⟦ σ , x , suc f ⟧↦⟦ σ' , this' , f ⟧) → fuelLL' (x ⋯ that) (seqstep hlstep) ≡ fuelLL' x hlstep
  seqstp≡ assign = refl
  seqstp≡ seqskip = refl
  seqstp≡ (seqstep hlstep) = refl
  seqstp≡ (iftrue x) = refl
  seqstp≡ (iffalse x) = refl
  seqstp≡ (whilefalse x) = refl
  seqstp≡ (whiletrue x) = refl


--Fuel Calc BigStep

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

  emptyBS : ∀ {I σ} → fuelLLBS {I = I} {σ = σ} Empty ≡ 0
  emptyBS = refl


 
{-
  fuelBSlem1 : ∀ {I f' f σ σ'} → (sem : ⟦ I , σ , suc f ⟧⇛⟦ σ' , f' ⟧) → ∃[ x ] (fuelLLBS sem ≡ x ℕ+ f)
  fuelBSlem1 Skip = 1 ∣ refl
  fuelBSlem1 {_ ≔ a} {f'} Assign = suc (size` (acomp a)) ∣ refl
  fuelBSlem1 (Seq {f = f} {ℕ.zero} {.0} sem Empty) with fuelBSlem1 sem
  ... | x ∣ prf rewrite prf | +0 (x ℕ+ f) = x ∣ refl
  fuelBSlem1 (Seq {f = f} {suc f'} {f''} sem sem') with fuelBSlem1 sem | fuelBSlem1 sem'
  ... | x ∣ prf | x' ∣ prf' rewrite sym (+assoc (fuelLLBS' sem) (fuelLLBS' sem') f'') | prf' | +comm x' f' | +assoc (fuelLLBS' sem) f' x' = x' ℕ+ x ∣ suc-injective {!!} --suc-injective (helper (fuelLLBS' sem) f' x f x' prf)
    where{-
    helper : ∀ v w x y z → v ℕ+ suc w ≡ x ℕ+ y → suc (v ℕ+ w ℕ+ z) ≡ suc (z ℕ+ x ℕ+ y)
    helper v w x y z prf rewrite NatLem1 v w z | prf = {!!}-}
  fuelBSlem1 (IfFalse x sem) = {!!}
  fuelBSlem1 (IfTrue x sem) = {!!}
  fuelBSlem1 (WhileFalse x) = {!!}
  fuelBSlem1 (WhileTrue x sem sem₁) = {!!}

-}
