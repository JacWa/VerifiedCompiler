module Proofs.VerifiedCompilation where

  open import Proofs.NatProofs
  open import Proofs.Expr
  open import Proofs.Stack
  open import Proofs.ArithSemantics
  open import Proofs.Fuel

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc) hiding (_≟_)
  open import Data.Bool
  open import Data.Maybe
  open import Data.Empty

  open import Base.DataStructures
  open import Misc.Base

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Relation.Binary
  open import Relation.Nullary



  mutual
    Lemma2 : ∀ b Q {f s σ} → bexe b σ ≡ false → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , (size` (bcomp b false (size Q))) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q) & Q)) , f ⟧
    Lemma2 (BOOL x) y z rewrite z = some (⊢JMP refl) none
    Lemma2 (NOT x) y z = Lemma2' x y (notfalse z)
    Lemma2 (x AND x₁) y z = {!!}
    Lemma2 (x LT x₁) y z = {!!}

    postulate
      Lemma2' : ∀ b Q {f s σ} → bexe b σ ≡ true → (bcomp b true (size Q) & Q) ⊢⟦ config σ s (+ 0) , (size` (bcomp b true (size Q))) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b true (size Q) & Q)) , f ⟧
  
  postulate    
    Lemma3 : ∀ b Q {f f' s σ} → bexe b σ ≡ true  → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q)))     , f' ⟧
 


{-  Lemma2 : ∀ {c f s b σ} → bexe b σ ≡ false → compile (WHILE b DO c) ⊢⟦ config σ s (+ 0) , fᴴᴸ2ᴸᴸ (WHILE b DO c) (suc f) ⟧⇒*⟦ config σ s (size (compile (WHILE b DO c))) , f ⟧
  Lemma2 {c} {f} {b = BOOL false} prf rewrite +comm f 1 | size`&+ {compile c} {JMP -[1+ size` (compile c) ℕ+ 1 ] :: []} = some (⊢JMP refl) none
  Lemma2 {b = BOOL true} ()
  Lemma2 {b = NOT b} prf = {!!}
  Lemma2 {b = a AND b} {σ} prf with (bexe a σ) ≟ true
  Lemma2 {s = _} {a AND b} {σ} prf | yes p = {!!}
  Lemma2 {s = _} {a AND b} {σ} prf | no ¬p = {!!}
  Lemma2 {b = x LT x₁} prf = {!!}
-}
-----------------
-- Final Proof --
-----------------


  Lemma : ∀ I {σ f σᴴᴸ σᴸᴸ f'} → (semᴴᴸ : ⟦ σ , I , f ⟧↦*⟦ σᴴᴸ , SKIP , f' ⟧) → compile I ⊢⟦ config σ $ (+ 0) , fuelLL I f semᴴᴸ ⟧⇒*⟦ config σᴸᴸ $ (size (compile I)) , f' ⟧ → σᴸᴸ ≡ σᴴᴸ
  Lemma _ {f = 0} x w rewrite nofᴴ x | nofᴸ w = refl
  Lemma (SKIP) {f = suc f} (step () _)
  Lemma SKIP done x rewrite nothing≡σ x = refl
  Lemma (x ≔ a) {σ} {f = suc f} (step assign rest) w rewrite fuelSKIP f {rest = rest} | skipseqσ rest | skipseqf rest | size`&+ {acomp a} {STORE x :: []} | +comm (size` (acomp a)) 1 = Lemma1 {a} w 
  Lemma (WHILE b DO c) {σ} {suc f}_ _ with inspect (bexe b σ)
  Lemma (WHILE b DO c) {f = suc f} (step (whiletrue prf)  rest)  w | true with≡ _ rewrite prf = {!!}
  Lemma (WHILE b DO c) {σ} {suc f} (step (whilefalse prf) rest)  w | false with≡ _ rewrite prf | fuelSKIP f {rest = rest} | skipseqσ rest | skipseqf rest with Lemma2 b (compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) {f} {$} {σ} prf
  ... | z rewrite fuelSKIP f {rest = rest} | size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} = deterministic z w
  Lemma (WHILE b DO c) {_} (step (whiletrue x) rest) w | false with≡ y rewrite y = ⊥-elim (bool⊥ x)
  Lemma (WHILE b DO c) {_} {suc _} (step (whilefalse x) rest) w | true with≡ y rewrite x = ⊥-elim (bool⊥ y)
