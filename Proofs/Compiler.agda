module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Basic
  open import Proofs.NatProofs
  open import Misc.Base
  open import Base.DataStructures renaming (State to Store)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_) hiding (_<_)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Bool.Base
  open import Size
  open import Data.Maybe

  data Stateᴴᴸ : Set where
    stateᴴᴸ : Store → (fuel : ℕ) → Stateᴴᴸ

  {-# TERMINATING #-}
  storeᴴᴸ' : IExp → Stateᴴᴸ → Stateᴴᴸ
  storeᴴᴸ' i (stateᴴᴸ σ 0)                          = stateᴴᴸ σ 0
  storeᴴᴸ' SKIP                 (stateᴴᴸ σ (suc f)) = stateᴴᴸ σ f
  storeᴴᴸ' (x ≔ a)               (stateᴴᴸ σ (suc f)) = stateᴴᴸ ((x ≔ aexe a σ) ∷ σ) f
  storeᴴᴸ' (P ⋯ Q)               state = storeᴴᴸ' Q (storeᴴᴸ' P state)
  storeᴴᴸ' (IF b THEN P ELSE Q) (stateᴴᴸ σ (suc f)) with bexe b σ
  ... | true  = storeᴴᴸ' P (stateᴴᴸ σ f)
  ... | false = storeᴴᴸ' Q (stateᴴᴸ σ f)
  storeᴴᴸ' (WHILE b DO c)       (stateᴴᴸ σ (suc f)) with bexe b σ
  ... | true  = storeᴴᴸ' (c ⋯ (WHILE b DO c)) (stateᴴᴸ σ f)
  ... | false = stateᴴᴸ σ f

  storeᴴᴸ : IExp → ℕ → Store
  storeᴴᴸ i f with storeᴴᴸ' i (stateᴴᴸ ⟦⟧ f)
  ... | stateᴴᴸ σ f' = σ


  data Stateᴸᴸ : Set where
    stateᴸᴸ : Prog → Config → (fuel : ℕ) → Stateᴸᴸ

  getP : Stateᴸᴸ → Prog
  getP (stateᴸᴸ p _ _) = p
  
  getC : Stateᴸᴸ → Config
  getC (stateᴸᴸ _ c _) = c

  getF : Stateᴸᴸ → ℕ
  getF (stateᴸᴸ _ _ f) = f

  storeᴸᴸ' : Stateᴸᴸ → Stateᴸᴸ
  storeᴸᴸ' (stateᴸᴸ p (config σ stk pc) 0) = (stateᴸᴸ p (config σ stk pc) 0)
  storeᴸᴸ' (stateᴸᴸ p (config σ stk pc) (suc f)) with p ፦ pc
  ... | nothing = (stateᴸᴸ p (config σ stk pc) (suc f))
  ... | just i with i
  ... | LOADI n = {!!}

  storeᴸᴸ : Prog → (fuel : ℕ) → Store
  storeᴸᴸ [] f = ⟦⟧
  storeᴸᴸ (i :: is) f with storeᴸᴸ' (stateᴸᴸ (i :: is) (config ⟦⟧ $ (pos 0)) f)
  ... | stateᴸᴸ _ (config σ _ _) _ = σ

  {-# TERMINATING #-}
  fᴴᴸ2ᴸᴸ' : IExp → ℕ × ℕ × Store → ℕ × ℕ × Store
  fᴴᴸ2ᴸᴸ' _        (0 , fᴸᴸ , σ)         = (0 , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' SKIP     (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' (x ≔ a) (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , suc (fᴸᴸ ℕ+ size` (acomp a)) , ((x ≔ (aexe a σ)) ∷ σ))
  fᴴᴸ2ᴸᴸ' (P ⋯ Q) (suc fᴴᴸ , fᴸᴸ , σ) = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ2ᴸᴸ' P (suc fᴴᴸ , fᴸᴸ , σ))
  fᴴᴸ2ᴸᴸ' (IF b THEN P ELSE Q) ((suc fᴴᴸ) , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' P (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (pos 1)))) , σ)
  ... | false = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (pos 1)))) , σ)
  fᴴᴸ2ᴸᴸ' (WHILE b DO c) (suc fᴴᴸ , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' (c ⋯ (WHILE b DO c)) (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ pos 1))) , σ)
  ... | false = fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ pos 1))) , σ

  fᴴᴸ2ᴸᴸ : IExp → ℕ → ℕ
  fᴴᴸ2ᴸᴸ I fᴴᴸ with fᴴᴸ2ᴸᴸ' I (fᴴᴸ , 0 , ⟦⟧)
  ... | fᴴᴸ' , fᴸᴸ , _ = fᴴᴸ' ℕ+ fᴸᴸ

  Lemma0 : ∀ P fᴴᴸ → storeᴴᴸ P fᴴᴸ ≡ storeᴸᴸ (compile P) (fᴴᴸ2ᴸᴸ P fᴴᴸ)
  Lemma0 P 0 with compile P
  ... | [] = refl
  ... | (i :: is) = refl
  Lemma0 SKIP (suc f) = refl

