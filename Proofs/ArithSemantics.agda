module Proofs.ArithSemantics where

  open import Proofs.NatProofs
  open import Proofs.Stack
 

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc) hiding (_≟_)
  open import Data.Maybe using (just)

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


  Lemma1' : ∀ {a rest σ s f} → ((acomp a) & rest) ⊢⟦ config σ s (+ 0) , size` (acomp a & rest) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , size` rest ℕ+ f ⟧
  Lemma1' {a} {rest} {f = f} rewrite size`&+ {acomp a} {rest} | sym (+assoc (size` (acomp a)) (size` rest) (f)) = stacklem1 (Lemma1b' a)

  Lemma1'' : ∀ {a rest σ s f} → ((acomp a) & rest) ⊢⟦ config σ s (+ 0) , size` (acomp a) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , f ⟧
  Lemma1'' {a} = stacklem1 (Lemma1b' a)

  Lemma1''&Store : ∀ {a x rest σ s f} → (acomp a & STORE x :: rest) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config ((x ≔ (aexe a σ)) ∷ σ) s (+ suc (size` (acomp a))) , f ⟧
  Lemma1''&Store {a} {x} {rest} {σ} {s} {f} with Lemma1b' a {σ} {s} {suc f}
  ... | z rewrite +comm (size` (acomp a)) (suc f) | +comm f (size` (acomp a)) with stacklem1 {q = STORE x :: rest} z
  ... | z' = insertAtEnd z' (⊢STORE (stacklem2c (acomp a) (STORE x) rest))

  mutual
    ArithExec : ∀ {a this that σ s f} → (this & (acomp a) & that) ⊢⟦ config σ s (size this) , size` (acomp a) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a & this)) , f ⟧
    ArithExec {NAT x} {this} {that} = some (⊢LOADI (stacklem2c this (LOADI x) (that))) none
    ArithExec {VAR x} {this} {that} = some (⊢LOAD (stacklem2c this (LOAD x) (that))) none
    ArithExec {a + b} {this} {that} {σ} {f = f} rewrite sym (&assoc (acomp a) (acomp b & ADD :: []) (that)) | +comm (aexe a σ) (aexe b σ) | ArithExecAux2' {a} {b} {this} | size`&+ {acomp a} {acomp b & ADD :: []} | sym (+assoc (size` (acomp a)) (size` (acomp b & ADD :: [])) f) = insertAtEnd* (ArithExec {a}) (insertAtEnd (ArithExecAux1 {this} {a} {b}) (⊢ADD (ArithExecAux3 {this} {a} {b})))

    ArithExecAux1 : ∀ {this a b that σ s f} → (this & acomp a & (acomp b & ADD :: []) & that) ⊢⟦ config σ (aexe a σ , s) (size (acomp a & this)) , size` (acomp b & ADD :: []) ℕ+ f ⟧⇒*⟦ config σ (aexe b σ , aexe a σ , s) (size (acomp b & acomp a & this)) , suc f ⟧
    ArithExecAux1 {this} {a} {b} {that} {f = f} rewrite &assoc this (acomp a) ((acomp b & ADD :: []) & that) | sym (&assoc (acomp b) (ADD :: []) that) | size`&+ {acomp b} {acomp a & this} | size`trans (acomp a) this | sym (size`&+ {acomp b} {this & acomp a}) | size`&+ {acomp b} {ADD :: []} | sym (+assoc (size` (acomp b)) 1 f) = ArithExec {b}


    ArithExecAux2 : ∀ P Q R S → size` ((P & Q & R) & S) ≡ size` R ℕ+ (size` (Q & P & S))
    ArithExecAux2 P Q R S rewrite size`&+ {Q} {P & S} | size`&+ {P} {S} | +assoc (size` Q) (size` P) (size` S) | +comm (size` Q) (size` P) | +assoc (size` R) (size` P ℕ+ size` Q) (size` S) | +comm (size` R) (size` P ℕ+ size` Q) | sym (+assoc (size` P) (size` Q) (size` R)) | sym (size`&+ {Q} {R}) | sym (size`&+ {P} {Q & R}) | sym (size`&+ {P & Q & R} {S}) = refl

    ArithExecAux2' : ∀ {a b this} → (size` ((acomp a & acomp b & ADD :: []) & this)) ≡ (suc (size` (acomp b & acomp a & this)))
    ArithExecAux2' {a} {b} {this} = ArithExecAux2 (acomp a) (acomp b) (ADD :: []) this

    ArithExecAux3 : ∀ {this a b that} → ((this & acomp a & (acomp b & ADD :: []) & that) ፦ (+ size` (acomp b & acomp a & this))) ≡ just ADD
    ArithExecAux3 {this} {a} {b} {that} rewrite sym (&assoc (acomp b) (ADD :: []) that) | &assoc (acomp a) (acomp b) (ADD :: that) | &assoc this (acomp a & acomp b) (ADD :: that) | size`&+ {acomp b} {acomp a & this} | size`&+ {acomp a} {this} | +comm (size` (acomp a)) (size` this) | +assoc (size` (acomp b)) (size` this) (size` (acomp a)) | +comm (size` (acomp b)) (size` this) | sym (+assoc (size` this) (size` (acomp b)) (size` (acomp a))) | +comm (size` (acomp b)) (size` (acomp a)) | sym (size`&+ {acomp a} {acomp b}) | sym (size`&+ {this} {acomp a & acomp b}) = stacklem2c (this & acomp a & acomp b) ADD that
  

  

