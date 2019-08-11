module Proofs.Stack.Determinism where

  open import Lang.Stack
  
  open import Base.DataStructures
  open import Base.Inspect
  
  open import Misc.Base
  
  open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_)
  open import Agda.Builtin.Equality
  
  open import Data.Nat.Base
  open import Data.String renaming (_≟_ to streqdec)
  open import Data.Maybe
  open import Data.Empty
  open import Data.Bool
  open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; +-comm; +-assoc)
  open import Data.Nat.Properties using (≤-refl; ≤-trans)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_; _<_)
  
  open import Proofs.Basic
  open import Proofs.NatProofs
  open import Proofs.Stack
  
  open import Relation.Binary
  open import Relation.Nullary using (¬_; Dec; yes; no)

  open import Semantics.LowLevel


  ------------------------
  -- Determinism of SML --
  ------------------------

  just≡ : {i j : Inst} → _≡_ {A = Maybe Inst} (just i) (just j) → i ≡ j
  just≡ refl = refl

  detstep-nothing :  ∀ {x xs σ s pc f c' f'} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ → (x :: xs) ፦ pc ≡ nothing → ⊥
  detstep-nothing (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢STORE x) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢ADD x) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-nothing (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  LOADI≡ : ∀ {n n'} → LOADI n ≡ LOADI n' → n' ≡ n
  LOADI≡ {n} {n'} prf with Data.Nat.Base._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  LOADI≡ refl | no prf' = refl
  
  detstep-justloadi :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOADI n) → c'' ≡ c'
  detstep-justloadi (⊢LOADI x) (⊢LOADI y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOADI≡ w | LOADI≡ w' = refl
  detstep-justloadi (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justloadi (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justloadi (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justloadi sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-justloadi sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-justloadi sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  LOAD≡ : ∀ {x x'} → LOAD x ≡ LOAD x' → x' ≡ x
  LOAD≡ {x} {x'} prf with streqdec x x'
  ... | yes prfₙ = sym (prfₙ)
  LOAD≡ refl | no prf' = refl
  
  detstep-justload :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOAD n) → c'' ≡ c'
  detstep-justload (⊢LOAD x) (⊢LOAD y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOAD≡ w | LOAD≡ w' = refl
  detstep-justload (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justload (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justload (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justload sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-justload sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-justload sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  
  detstep-justadd :  ∀ {x xs σ s pc f c' f' c'' f''} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just ADD → c'' ≡ c'
  detstep-justadd (⊢ADD x) (⊢ADD y) prf = refl
  detstep-justadd (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justadd (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justadd (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justadd sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep-justadd sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-justadd sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  STORE≡ : ∀ {x x'} → STORE x ≡ STORE x' → x' ≡ x
  STORE≡ {x} {x'} prf with streqdec x x'
  ... | yes prfₙ = sym (prfₙ)
  STORE≡ refl | no prf' = refl
  
  detstep-juststore :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (STORE n) → c'' ≡ c'
  detstep-juststore (⊢STORE x) (⊢STORE y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite STORE≡ w | STORE≡ w' = refl
  detstep-juststore (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-juststore (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-juststore (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep-juststore sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-juststore sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-juststore sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  JMP≡ : ∀ {n n'} → JMP n ≡ JMP n' → n' ≡ n
  JMP≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMP≡ refl | no prf' = refl
  
  detstep-justjmp :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMP n) → c'' ≡ c'
  detstep-justjmp (⊢JMP x) (⊢JMP y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMP≡ w | JMP≡ w' = refl
  detstep-justjmp (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmp (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmp (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justjmp sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-justjmp sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-justjmp sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  JMPGE≡ : ∀ {n n'} → JMPGE n ≡ JMPGE n' → n' ≡ n
  JMPGE≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMPGE≡ refl | no prf' = refl
  
  detstep-justjmpge :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPGE n) → c'' ≡ c'
  detstep-justjmpge (⊢JMPGEtrue x _) (⊢JMPGEtrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep-justjmpge (⊢JMPGEfalse x _) (⊢JMPGEfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep-justjmpge (⊢JMPGEfalse _ lt) (⊢JMPGEtrue _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep-justjmpge (⊢JMPGEtrue _ ge) (⊢JMPGEfalse _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep-justjmpge (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpge (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmpge (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmpge (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpge (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpge (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpge (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpge sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep-justjmpge sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justjmpge sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-justjmpge sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-justjmpge sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justjmpge sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep-justjmpge sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()

  JMPLESS≡ : ∀ {n n'} → JMPLESS n ≡ JMPLESS n' → n' ≡ n
  JMPLESS≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMPLESS≡ refl | no prf' = refl
  
  detstep-justjmpless :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPLESS n) → c'' ≡ c'
  detstep-justjmpless (⊢JMPLESStrue x _) (⊢JMPLESStrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep-justjmpless (⊢JMPLESSfalse x _) (⊢JMPLESSfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep-justjmpless (⊢JMPLESSfalse _ ge) (⊢JMPLESStrue _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep-justjmpless (⊢JMPLESStrue _ lt) (⊢JMPLESSfalse _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep-justjmpless (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpless (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmpless (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep-justjmpless (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpless (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpless (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpless (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep-justjmpless sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep-justjmpless sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep-justjmpless sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep-justjmpless sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep-justjmpless sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  detstep-justjmpless sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep-justjmpless sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()

  detstep-c : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ →  p ⊢⟦ c , f ⟧⇒⟦ c'' , f'' ⟧ → c'' ≡ c'
  detstep-c {[]}  (⊢LOADI ()) sem2 
  detstep-c {[]}  (⊢LOAD ()) sem2
  detstep-c {[]}  (⊢STORE ()) sem2
  detstep-c {[]}  (⊢ADD ()) sem2
  detstep-c {[]}  (⊢JMP ()) sem2
  detstep-c {[]}  (⊢JMPLESSfalse () x₁) sem2
  detstep-c {[]}  (⊢JMPLESStrue () x₁) sem2
  detstep-c {[]}  (⊢JMPGEtrue () x₁) sem2
  detstep-c {[]}  (⊢JMPGEfalse () x₁) sem2
  detstep-c {x :: xs} {c} {0} sem1 () 
  detstep-c {x :: xs} {config σ s pc} {suc f} sem1 sem2 with inspect ((x :: xs) ፦ pc)
  ... | nothing with≡ prf = ⊥-elim (detstep-nothing sem1 prf)
  ... | (just i) with≡ prf with i
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOADI x₁ = detstep-justloadi sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOAD x₁ = detstep-justload sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | ADD = detstep-justadd sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | STORE x₁ = detstep-juststore sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMP x₁ = detstep-justjmp sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPLESS x₁ = detstep-justjmpless sem1 sem2 prf
  detstep-c {x :: xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPGE x₁ = detstep-justjmpge sem1 sem2 prf
  

  deterministic-c : ∀ {p f c c' f' c''} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ →  p ⊢⟦ c , f ⟧⇒*⟦ c'' , f' ⟧ → c'' ≡ c'
  deterministic-c none none = refl
  deterministic-c {f = 0} _ (some () rest)
  deterministic-c {f = suc f} none (some one rest) with fdecone one
  ... | z rewrite z with fdec rest
  ... | p = ⊥-elim (s≤→⊥ p)
  deterministic-c {f = 0} (some () rest) _
  deterministic-c {f = suc f} (some one rest) none with fdecone one
  ... | z rewrite z with fdec rest
  ... | p = ⊥-elim (s≤→⊥ p)
  deterministic-c {f = suc f} (some one rest) (some one' rest') rewrite detstep-c one one' | fdecone one | fdecone one' = deterministic-c rest rest'
  
  deterministic-σ : ∀ {p f f' σ s pc σ' s' pc' σ'' s'' pc''} → p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ →  p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ'' s'' pc'' , f' ⟧ → σ'' ≡ σ'
  deterministic-σ sem1 sem2 with deterministic-c sem1 sem2
  ... | refl = refl
  deterministic-pc : ∀ {p f f' σ s pc σ' s' pc' σ'' s'' pc''} → p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ →  p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ'' s'' pc'' , f' ⟧ → pc'' ≡ pc'
  deterministic-pc sem1 sem2 with deterministic-c sem1 sem2
  ... | refl = refl
