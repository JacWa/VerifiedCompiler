module Proofs.VerifiedCompilation where

  open import Proofs.NatProofs
  open import Proofs.Expr
  open import Proofs.Stack

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc) hiding (_≟_)
  open import Data.Bool
  open import Data.Maybe

  open import Base.DataStructures
  open import Misc.Base

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Relation.Binary


--------------------------------------------------------------------
-- Lemma(1)'s -- Proofs for semantics over arithmetic expressions --
--------------------------------------------------------------------

  Lemma1a : ∀ a x σ σ' s f → (acomp a) ⊢⟦ config σ s (+ 0) , suc (f ℕ+ size` (acomp a)) ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , suc f ⟧ → ((acomp a) & STORE x :: []) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ' s (+ suc (size` (acomp a))) , f ⟧ → σ' ≡ ((x ≔ (aexe a σ)) ∷ σ)
  Lemma1a a x σ σ' s f asem sem with (stacklem1 {q = STORE x :: []} asem)
  ... | w with insertAtEnd w (⊢STORE {x = x} (pclem1 {acomp a} {STORE x :: []} {+ 0}))
  ... | w' rewrite +comm f (size` (acomp a)) with deterministic w' sem
  ... | w'' rewrite w'' = σ≡ w'' 

  Lemma1f : ∀ e {p c f c' f'} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → p ⊢⟦ c , e ℕ+ f ⟧⇒⟦ c' , e ℕ+ f' ⟧
  Lemma1f n {f' = f'} (⊢LOADI x) rewrite +comm n (suc f') | +comm n f' = ⊢LOADI x
  Lemma1f n {f' = f'} (⊢LOAD x₁) rewrite +comm n (suc f') | +comm n f' = ⊢LOAD x₁
  Lemma1f n {f' = f'} (⊢STORE x₁) rewrite +comm n (suc f') | +comm n f' = ⊢STORE x₁
  Lemma1f n {f' = f'} (⊢ADD x) rewrite +comm n (suc f') | +comm n f' = ⊢ADD x
  Lemma1f n {f' = f'} (⊢JMP x) rewrite +comm n (suc f') | +comm n f' = ⊢JMP x
  Lemma1f n {f' = f'} (⊢JMPLESSfalse x x₁) rewrite +comm n (suc f') | +comm n f' = ⊢JMPLESSfalse x x₁
  Lemma1f n {f' = f'} (⊢JMPLESStrue x x₁) rewrite +comm n (suc f') | +comm n f' = ⊢JMPLESStrue x x₁
  Lemma1f n {f' = f'} (⊢JMPGEtrue x x₁) rewrite +comm n (suc f') | +comm n f' = ⊢JMPGEtrue x x₁
  Lemma1f n {f' = f'} (⊢JMPGEfalse x x₁) rewrite +comm n (suc f') | +comm n f' = ⊢JMPGEfalse x x₁

  Lemma1e : ∀ e {p c f c' f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , e ℕ+ f ⟧⇒*⟦ c' , e ℕ+ f' ⟧
  Lemma1e n none = none
  Lemma1e n (some one rest) = some (Lemma1f n one) (Lemma1e n rest)


  Lemma1c' : ∀ P b {σ s f σ' s'} → P ⊢⟦ config σ s (+ 0) , (size` P ℕ+ f) ⟧⇒*⟦ config σ' s' (size P) , f ⟧ →  (P & acomp b) ⊢⟦ config σ s (+ 0) , (size` (P & acomp b) ℕ+ f) ⟧⇒*⟦ config σ' (aexe b σ' , s') (size (P & acomp b)) , f ⟧
  Lemma1c' P (NAT n) p with Lemma1e 1 (stacklem1 {q = acomp (NAT n)} p) 
  ... | w' rewrite +comm (size` P) 1 | size`&+ {P} {LOADI n :: []} | +comm (size` P) 1 = insertAtEnd w' (⊢LOADI (stacklem2c P (LOADI n) []))
  Lemma1c' P (VAR x) p with Lemma1e 1 (stacklem1 {q = acomp (VAR x)} p) 
  ... | w' rewrite +comm (size` P) 1 | size`&+ {P} {LOAD x :: []} | +comm (size` P) 1 = insertAtEnd w' (⊢LOAD (stacklem2c P (LOAD x) []))
  Lemma1c' P (m + n) {σ' = σ'} p rewrite &assoc P (acomp m) (acomp n & ADD :: []) | &assoc (P & acomp m) (acomp n) (ADD :: []) with Lemma1c' P m p
  ... | w with Lemma1c' (P & (acomp m)) n w
  ... | w' with stacklem1 {q = ADD :: []} w'
  ... | w'' with Lemma1e 1 w''
  ... | w''' rewrite size`&+ {(P & acomp m) & acomp n} {ADD :: []} | +comm (size` ((P & acomp m) & acomp n)) 1 | +comm (aexe m σ') (aexe n σ') = insertAtEnd {(((P & acomp m) & acomp n) & ADD :: [])} w''' (⊢ADD (stacklem2c ((P & acomp m) & acomp n) ADD []))
  
  Lemma1b' : ∀ a {σ s f} → (acomp a) ⊢⟦ config σ s (+ 0) , (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ (aexe a σ , s) (+ size` (acomp a)) , f ⟧
  Lemma1b' (NAT n) = some (⊢LOADI refl) none
  Lemma1b' (VAR x) = some (⊢LOAD refl) none
  Lemma1b' (a + b) {σ} {s} {f} with stacklem1 {q = ADD :: []} (Lemma1e 1 (Lemma1c' (acomp a) b {σ} {s} {f} (Lemma1b' a)))
  ... | w rewrite &assoc (acomp a) (acomp b) (ADD :: []) | size`&+ {acomp a & acomp b} {ADD :: []} | size`&+ {acomp a} {acomp b} | +comm (size` (acomp a) ℕ+ size` (acomp b)) 1 | +comm (aexe a σ) (aexe b σ) | sym (size`&+ {acomp a} {acomp b}) = insertAtEnd w (⊢ADD (stacklem2c (acomp a & acomp b) ADD []))

  Lemma1b : ∀ a σ s f → (acomp a) ⊢⟦ config σ s (+ 0) , (f ℕ+ size` (acomp a)) ⟧⇒*⟦ config σ (aexe a σ , s) (+ size` (acomp a)) , f ⟧
  Lemma1b a σ s f rewrite +comm f (size` (acomp a)) = Lemma1b' a

  Lemma1 : ∀ {a x σ f σᴸᴸ} → ((acomp a) & STORE x :: []) ⊢⟦ config σ $ (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σᴸᴸ $ (+ suc (size` (acomp a))) , f ⟧  → σᴸᴸ ≡ ((x ≔ (aexe a σ)) ∷ σ)
  Lemma1 {a} {x} {σ} {f} {σᴸᴸ} w rewrite Lemma1a a x σ σᴸᴸ $ f (Lemma1b a σ $ (suc f)) w = refl



-----------------
-- Final Proof --
-----------------


  Lemma : ∀ I {σ f σᴴᴸ σᴸᴸ f'} → ⟦ σ , I , f ⟧↦*⟦ σᴴᴸ , SKIP , f' ⟧ → compile I ⊢⟦ config σ $ (+ 0) , fᴴᴸ2ᴸᴸ I f ⟧⇒*⟦ config σᴸᴸ $ (+ (fᴴᴸ2ᴸᴸ I f ∸ f')) , f' ⟧ → σᴸᴸ ≡ σᴴᴸ
  Lemma _ {f = 0} done none = refl
  Lemma _ {f = 0} done (some () _)
  Lemma (SKIP) {f = suc f} (step () _)
  Lemma (x ≔ a) {σ} {f = suc f} (step assign done) w rewrite +comm f (suc (size` (acomp a))) | +- (suc (size` (acomp a))) f | Lemma1 {a} w = refl
{-
  Lemma (x ≔ (NAT n)) {f = suc f} (step assign done) w rewrite +comm f 2 | +- 2 f with w
  ... | some (⊢LOADI refl) (some (⊢STORE refl) none) = refl
  ... | some (⊢LOADI refl) (some (⊢LOADI ()) _)
  ... | some (⊢LOADI refl) (some (⊢LOAD ()) _)
  ... | some (⊢LOADI refl) (some (⊢STORE refl) (some (⊢LOADI ()) _))
  ... | some (⊢LOADI refl) (some (⊢STORE refl) (some (⊢LOAD ()) _))
  ... | some (⊢LOADI refl) (some (⊢STORE refl) (some (⊢JMP ()) _))
  ... | some (⊢LOADI refl) (some (⊢JMP ()) _)
  ... | some (⊢LOAD ()) _
  ... | some (⊢JMP ()) _
  Lemma (x ≔ (VAR y)) {f = suc f} (step assign done) w rewrite +comm f 2 | +- 2 f with w
  ... | some (⊢LOAD refl) (some (⊢STORE refl) none) = refl
  ... | some (⊢LOAD refl) (some (⊢LOADI ()) _)
  ... | some (⊢LOAD refl) (some (⊢LOAD ()) _)
  ... | some (⊢LOAD refl) (some (⊢STORE refl) (some (⊢LOADI ()) _))
  ... | some (⊢LOAD refl) (some (⊢STORE refl) (some (⊢LOAD ()) _))
  ... | some (⊢LOAD refl) (some (⊢STORE refl) (some (⊢JMP ()) _))
  ... | some (⊢LOAD refl) (some (⊢JMP ()) _)
  ... | some (⊢LOADI ()) _
  ... | some (⊢JMP ()) _
  Lemma (x ≔ (a + b)) {σ} {f = suc f} (step assign done) w rewrite +comm f (suc (size` (acomp a & acomp b & ADD :: []))) | +- (suc (size` (acomp a & acomp b & ADD :: []))) f | Lemma1 {a + b} w = refl
-}
  Lemma (WHILE b DO c) {σ} _ _ with bexe b σ
  Lemma (WHILE b DO c) {f = suc f} (step (whiletrue prf)  rest)  _ | true  rewrite prf = {!!}
  Lemma (WHILE b DO c) {f = suc f} (step (whilefalse prf) rest)  _ | false rewrite prf = {!!}
  






{-
  


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
-}
