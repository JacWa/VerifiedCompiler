module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack renaming (JMPLESS to JMPLT)
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

  {-# TERMINATING #-}
  storeᴸᴸ' : Stateᴸᴸ → Stateᴸᴸ
  storeᴸᴸ' (stateᴸᴸ p (config σ stk pc) (suc f)) with p ፦ pc
  ... | nothing = stateᴸᴸ p (config σ stk pc) (suc f)
  ... | just i with i
  ... | LOADI n = storeᴸᴸ' (stateᴸᴸ p (config σ (n , stk) (pc z+ pos 1)) f)
  ... | LOAD  x = storeᴸᴸ' (stateᴸᴸ p (config σ (get-var x σ , stk) (pc z+ pos 1)) f)
  ... | ADD     = storeᴸᴸ' (stateᴸᴸ p (config σ ((hd stk ℕ+ hd (tl stk)) , tl (tl stk)) ((pc z+ pos 1))) f)
  ... | STORE x = storeᴸᴸ' (stateᴸᴸ p (config ((x ≔ (hd stk)) ∷ σ) (tl stk) ((pc z+ pos 1))) f)
  ... | JMP x   = storeᴸᴸ' (stateᴸᴸ p (config σ stk (pc z+ pos 1 z+ x)) f)
  ... | JMPLT x with is hd stk ≤ hd (tl stk)
  ... | true  = storeᴸᴸ' (stateᴸᴸ p (config σ (tl (tl stk)) (pc z+ pos 1)) f)
  ... | false = storeᴸᴸ' (stateᴸᴸ p (config σ (tl (tl stk)) (pc z+ pos 1 z+ x)) f)
  storeᴸᴸ' (stateᴸᴸ p (config σ stk pc) (suc f)) | just i | JMPGE x with is hd stk ≤ hd (tl stk)
  ... | true  = storeᴸᴸ' (stateᴸᴸ p (config σ (tl (tl stk)) (pc z+ pos 1 z+ x)) f)
  ... | false = storeᴸᴸ' (stateᴸᴸ p (config σ (tl (tl stk)) (pc z+ pos 1)) f)
  storeᴸᴸ' (stateᴸᴸ p (config σ stk pc) 0) = (stateᴸᴸ p (config σ stk pc) 0)
  
  storeᴸᴸ : Prog → (fuel : ℕ) → Store
  storeᴸᴸ P f with storeᴸᴸ' (stateᴸᴸ P (config ⟦⟧ $ (pos 0)) f)
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

-------------------------
-- Intermediary Proofs --
-------------------------

  σnothing : ∀ {σ σ' stk f} → storeᴸᴸ' (stateᴸᴸ [] (config σ stk (pos 0)) f) ≡ storeᴸᴸ' (stateᴸᴸ [] (config σ' stk (pos 0)) f) → σ ≡ σ'
  σnothing {σ} {σ'} {stk}  nope = {!!}

  AddRightᴸᴸ : ∀ P Q {σ stk σ' stk'} f → storeᴸᴸ' (stateᴸᴸ P (config σ stk (pos 0)) (size` P ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ P (config σ' stk' (size P)) f) → storeᴸᴸ' (stateᴸᴸ (P & Q) (config σ stk (pos 0)) (size` P ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (P & Q) (config σ' stk' (size P)) f)
  AddRightᴸᴸ P [] f pexec rewrite &[] {P} = pexec
  AddRightᴸᴸ [] (i :: Q) f pexec rewrite +comm 1 1  = {!!}


{-
{-
  Lemma2 : ∀ P Q {σ stk σ' stk'} f → storeᴸᴸ' (stateᴸᴸ Q (config σ stk (pos 0)) (size` Q ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ Q (config σ' stk' (size  Q)) f) → storeᴸᴸ' (stateᴸᴸ (P & Q) (config σ stk (size P)) (size` Q ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (P & Q) (config σ' stk' (size (P & Q))) f)
  Lemma2 = {!!}
-}

  Lemma3 : ∀ i P {σ stk σ' stk'} f → storeᴸᴸ' (stateᴸᴸ P (config σ stk (pos 0)) (size` P ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ P (config σ' stk' (size P)) f) → storeᴸᴸ' (stateᴸᴸ (i :: P) (config σ stk (pos 1)) (size` P ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (i :: P) (config σ' stk' (pos 1 z+ size P)) f)
  Lemma3 = {!!}

  -- For prog `P & Q & rest` given `Q & rest ⊢ state'[pc = pos 0] → state''` then `P & Q & rest ⊢ state'[pc = pos 0] → state''[pc = size P + size Q]`
  Lemma1 : ∀ P Q rest {σ' stk' σ'' stk''} f → storeᴸᴸ' (stateᴸᴸ (Q & rest) (config σ' stk' (pos 0)) (size` Q ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (Q & rest) (config σ'' stk'' (size Q)) f) → storeᴸᴸ' (stateᴸᴸ (P & Q & rest) (config σ' stk' (size P)) (size` Q ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (P & Q & rest) (config σ'' stk'' (size P z+ size Q)) f)
  Lemma1 [] Q rest f qexec = qexec
  Lemma1 (x :: xs) Q rest f qexec = Lemma3 x {!!} {!f!} {!!}
  -}


-------------------------------------------------------------------------------------------------------------------

  ≔Lemma1 : ∀ P q qs → (P & (q :: qs)) ፦ size P ≡ just q
  ≔Lemma1 [] q qs = refl
  ≔Lemma1 (x :: xs) q qs rewrite ≔Lemma1 xs q qs = refl

  ≔Lemma2 : ∀ P → P ፦ size P ≡ nothing
  ≔Lemma2 [] = refl
  ≔Lemma2 (x :: xs) rewrite ≔Lemma2 xs = refl
  
  ≔Lemma3,1 : ∀ P Q → size` (P & Q) ≡ size` P ℕ+ size` Q
  ≔Lemma3,1 [] Q = refl
  ≔Lemma3,1 (x :: xs) Q rewrite ≔Lemma3,1 xs Q = refl

  ≔Lemma3 : ∀ P Q → size (P & Q) ≡ pos (size` P ℕ+ size` Q)
  ≔Lemma3 [] Q = refl
  ≔Lemma3 (x :: xs) Q rewrite ≔Lemma3,1 xs Q = refl

  ≔Lemma3` : ∀ P Q → pos (size` P ℕ+ size` Q) ≡ size (P & Q) 
  ≔Lemma3` P Q = sym (≔Lemma3 P Q)

  ≔Lemma0 : ∀ a rest σ stk f → storeᴸᴸ' (stateᴸᴸ (acomp a & rest) (config σ stk (pos 0)) (size` (acomp a) ℕ+ f)) ≡ storeᴸᴸ' (stateᴸᴸ (acomp a & rest) (config σ ((aexe a σ) , stk) (size (acomp a))) f)
  ≔Lemma0 (NAT n) _ _ _ _ = refl
  ≔Lemma0 (VAR x) _ _ _ _ = refl
  ≔Lemma0 (a + b) rest σ stk f rewrite ≔Lemma3,1 (acomp a) (acomp b & (ADD :: [])) | &assoc (acomp a) (acomp b & ADD :: []) rest | sym (+assoc (size` (acomp a)) (size` (acomp b & ADD :: [])) f) | ≔Lemma0 a ((acomp b & ADD :: []) & rest) σ stk (size` (acomp b & ADD :: []) ℕ+ f) | ≔Lemma3,1 (acomp b) (ADD :: []) | sym (+assoc (size` (acomp b)) 1 f) | &assoc (acomp b) (ADD :: []) rest = {!!}



--| Lemma1 (acomp a) (acomp b) (ADD :: rest) (suc f) (≔Lemma0 b (ADD :: rest) σ (aexe a σ , stk) (suc f)) | sym (&assoc (acomp a) (acomp b) (ADD :: rest)) | ≔Lemma3` (acomp a) (acomp b) | ≔Lemma1 ((acomp a) & (acomp b)) ADD rest | +comm (aexe a σ) (aexe b σ) | +assoc (size` (acomp a)) (size` (acomp b)) 1 | ≔Lemma3,1 (acomp a) (acomp b) = refl


-----------------
-- Final proof --
-----------------


  Lemma0 : ∀ P fᴴᴸ → storeᴴᴸ P fᴴᴸ ≡ storeᴸᴸ (compile P) (fᴴᴸ2ᴸᴸ P fᴴᴸ)
  Lemma0 P 0 with compile P
  ... | [] = refl
  ... | (i :: is) = refl
  Lemma0 SKIP (suc f) with f
  ... | 0 = refl
  ... | suc _ = refl
  Lemma0 (x ≔ a) (suc f) rewrite sucswap f (size` (acomp a)) | ≔Lemma0 a (STORE x :: []) ⟦⟧ $ (suc f) | ≔Lemma1 (acomp a) (STORE x) [] with f
  ... | 0 = refl
  ... | suc f' rewrite sym (≔Lemma3 (acomp a) (STORE x :: [])) | ≔Lemma2 ((acomp a) & STORE x :: []) = refl



{-
{-with storeᴸᴸ' (stateᴸᴸ (LOADI n :: STORE x :: []) (config ⟦⟧ $ (pos 0)) (suc (suc f)))
  ... | q -} with pos 1 z+ pos 1
  ... | pos 2 = {!refl!}

-}
