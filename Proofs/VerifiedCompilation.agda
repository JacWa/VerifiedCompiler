module Proofs.VerifiedCompilation where

  open import Proofs.NatProofs
  open import Proofs.Expr
  open import Proofs.Stack

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc)

  open import Base.DataStructures
  open import Misc.Base

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Data.Maybe

  open import Agda.Builtin.Bool



  


  join* : ∀ {P Q f σ s σ' s' σ'' s''} → P ⊢⟦ config σ s (+ 0) , (size` P ℕ+ (size` Q ℕ+ f)) ⟧⇒*⟦ config σ' s' (size P) , (size` Q ℕ+ f) ⟧ → Q ⊢⟦ config σ' s' (+ 0) , (size` Q ℕ+ f) ⟧⇒*⟦ config σ'' s'' (size Q) , f ⟧ → (P & Q) ⊢⟦ config σ s (+ 0) , ((size` (P & Q)) ℕ+ f) ⟧⇒*⟦ config σ'' s'' (size (P & Q)) , f ⟧
  join* {[]} none Q = Q
  join* {i :: is} (some I rest) Q = {!!}

  Lemma1 : ∀ a {σ s f} → acomp a ⊢⟦ config σ s (+ 0) , (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , f ⟧
  Lemma1 (NAT n) = some (⊢LOADI refl) none
  Lemma1 (VAR x) = some (⊢LOAD refl) none
  Lemma1 (m + n) {σ} rewrite &assoc (acomp m) (acomp n) (ADD :: []) | +comm (aexe m σ) (aexe n σ) = join* (join* (Lemma1 m) (Lemma1 n)) (some (⊢ADD refl) none)

  ≔-helper1 : ∀ a f x → size` (acomp a & STORE x :: []) ℕ+ f ≡ fᴴᴸ2ᴸᴸ (x ≔ a) (suc f)
  ≔-helper1 a f x rewrite size`&+ {acomp a} {STORE x :: []} | +comm (size` (acomp a)) 1 | +comm (suc (size` (acomp a))) f = refl

  Lemma2 : ∀ I f {σ σ' f'} → ⟦ σ , I , f ⟧↦⟦ σ' , SKIP , f' ⟧ → compile I ⊢⟦ config σ $ (+ 0) , fᴴᴸ2ᴸᴸ I f ⟧⇒*⟦ config σ' $ (+ (fᴴᴸ2ᴸᴸ I f ∸ f')) , f' ⟧
  Lemma2 _ 0 empty = none 
  Lemma2 (x ≔ a) (suc f) assign rewrite ≔-helper1 a f x | +comm f (suc (size` (acomp a))) | +- (suc (size` (acomp a))) f | +comm 1 (size` (acomp a)) | si1 (size` (acomp a)) f |  sym (size`&+ {acomp a} {STORE x :: []}) = join*(Lemma1 a)(some(⊢STORE refl)none)
--Lemma2 (x ≔ NAT n) (suc f) {f' = f'} assign rewrite +comm f' 2 | +- 2 f' = some (⊢LOADI refl) (some (⊢STORE refl) none)

  Lemma3 : ∀ I f {σ σ' f'} → compile I ⊢⟦ config σ $ (+ 0) , fᴴᴸ2ᴸᴸ I f ⟧⇒*⟦ config σ' $ (+ (fᴴᴸ2ᴸᴸ I f ∸ f')) , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ' , SKIP , f' ⟧
  Lemma3 _ 0 none = empty
  Lemma3 _ 0 (some () _)






  Lemma : ∀ I {σ f σᴴᴸ σᴸᴸ f'} → ⟦ σ , I , f ⟧↦⟦ σᴴᴸ , SKIP , f' ⟧ → compile I ⊢⟦ config σ $ (+ 0) , fᴴᴸ2ᴸᴸ I f ⟧⇒*⟦ config σᴸᴸ $ (+ (fᴴᴸ2ᴸᴸ I f ∸ f')) , f' ⟧ → σᴸᴸ ≡ σᴴᴸ
  Lemma _ {f = 0} empty none = refl
  Lemma _ {f = 0} empty (some () _)
  Lemma (SKIP) {f = suc f} ()
  Lemma (x ≔ a) {f = suc f} assign = {!!}
  Lemma (WHILE b DO c) {σ} _ _ with bexe b σ
  Lemma (WHILE b DO c) {f = suc f} WHILEtrue | true  = ?

