module Proofs.ArithSemantics where

  open import Proofs.NatProofs
  open import Proofs.Stack
 

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc) hiding (_≟_)

  open import Base.DataStructures
  open import Misc.Base

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  
--------------------------------------------------------------------
-- Lemma(1)'s -- Proofs for semantics over arithmetic expressions --
--------------------------------------------------------------------

  Lemma1a : ∀ a x σ σ' s f → (acomp a) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , suc f ⟧ → ((acomp a) & STORE x :: []) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ' s (+ suc (size` (acomp a))) , f ⟧ → σ' ≡ ((x ≔ (aexe a σ)) ∷ σ)
  Lemma1a a x σ σ' s f asem sem with (stacklem1 {q = STORE x :: []} asem)
  ... | w with insertAtEnd w (⊢STORE {x = x} (pclem1 {acomp a} {STORE x :: []} {+ 0} refl))
  ... | w' = deterministic w' sem

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


  Lemma1 : ∀ {a x σ f σᴸᴸ} → ((acomp a) & STORE x :: []) ⊢⟦ config σ $ (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σᴸᴸ $ (+ suc (size` (acomp a))) , f ⟧  → σᴸᴸ ≡ ((x ≔ (aexe a σ)) ∷ σ)
  Lemma1 {a} {x} {σ} {f} {σᴸᴸ} w with Lemma1b' a {σ} {$} {suc f}
  ... | w' rewrite +comm (size` (acomp a)) (suc f) | +comm f (size` (acomp a)) | Lemma1a a x σ σᴸᴸ $ f w' w = refl


