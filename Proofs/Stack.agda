module Proofs.Stack where

  open import Lang.Stack
  open import Base.DataStructures
  open import Data.Bool
  open import Data.Integer.Properties
  open import Misc.Base
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_)
  open import Agda.Builtin.Equality
  open import Data.Star
  open import Data.Nat.Base
  open import Data.Maybe
  open import Data.Empty
  open import Proofs.Basic
  open import Proofs.NatProofs
  open import Relation.Binary

  []&P≡P : ∀ P → [] & P ≡ P
  []&P≡P p = refl

  data _⊢⟦_,_⟧⇒⟦_,_⟧ : Prog → Config → ℕ → Config → ℕ → Set where
  
    ⊢LOADI        :        ∀ {p state stack pc n f} → (p ፦ (+ pc)) ≡ just (LOADI n)
                    ------------------------------------------------------------------------------
                     → p ⊢⟦ config state stack (+ pc) , suc f ⟧⇒⟦ config state (n , stack) (+ (suc pc)) , f ⟧


    ⊢LOAD         :        ∀ {p state stack pc x f} → (p ፦ (+ pc)) ≡ just (LOAD x)
                    ---------------------------------------------------------------------------------------------
                    → p ⊢⟦ config state stack (+ pc) , suc f ⟧⇒⟦ config state ((get-var x state) , stack) (+ (suc pc)) , f ⟧


    ⊢STORE        :          ∀ {p state n rest pc x f} → (p ፦ (+ pc)) ≡ just (STORE x)
                    ----------------------------------------------------------------------------------------
                    → p ⊢⟦ config state (n , rest) (+ pc) , suc f ⟧⇒⟦ config ((x ≔ n) ∷ state) rest (+ (suc pc)) , f ⟧


    ⊢ADD          :            ∀ {p state rest n1 n2 pc f} → (p ፦ (+ pc)) ≡ just ADD
                    -----------------------------------------------------------------------------------------------
                    → p ⊢⟦ config state (n1 , n2 , rest) (+ pc) , suc f ⟧⇒⟦ config state ((n1 + n2) , rest) (+ (suc pc)) , f ⟧


    ⊢JMP          :            ∀ {p state stack pc offset f} → (p ፦ (+ pc)) ≡ just (JMP offset)
                    -------------------------------------------------------------------------------------
                       → p ⊢⟦ config state stack (+ pc) , suc f ⟧⇒⟦ config state stack (+ (suc pc) z+ offset) , f ⟧


    ⊢JMPLESSfalse : ∀ {p state rest head next pc offset f} → (p ፦ (+ pc)) ≡ just (JMPLESS offset) → head ≤ next
                    ----------------------------------------------------------------------------------------------
                        → p ⊢⟦ config state (head , next , rest) (+ pc) , suc f ⟧⇒⟦ config state rest (+ (suc pc)) , f ⟧


    ⊢JMPLESStrue :  ∀ {p state rest head next pc offset f} → (p ፦ (+ pc)) ≡ just (JMPLESS offset) → head > next
                   -----------------------------------------------------------------------------------------------
                   → p ⊢⟦ config state (head , next , rest) (+ pc) , suc f ⟧⇒⟦ config state rest (+ (suc pc) z+ offset) , f ⟧


    ⊢JMPGEtrue    : ∀ {p state rest head next pc offset f} → (p ፦ (+ pc)) ≡ just (JMPGE offset) → head ≤ next
                   ------------------------------------------------------------------------------------------------
                   → p ⊢⟦ config state (head , next , rest) (+ pc) , suc f ⟧⇒⟦ config state rest (+ (suc pc) z+ offset) , f ⟧


    ⊢JMPGEfalse   : ∀ {p state rest head next pc offset f} → (p ፦ (+ pc)) ≡ just (JMPGE offset) → head > next
                   ---------------------------------------------------------------------------------------------
                     → p ⊢⟦ config state (head , next , rest) (+ pc) , suc f ⟧⇒⟦ config state rest (+ (suc pc)) , f ⟧



  data _⊢⟦_,_⟧⇒*⟦_,_⟧ : Prog → Config → ℕ → Config → ℕ → Set where

    none : ∀ {p c f}   --------------------------------------------
                                → p ⊢⟦ c , f ⟧⇒*⟦ c , f ⟧


    some : ∀ {p c c' c'' f f' f''} →   p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒*⟦ c'' , f'' ⟧ →
                                       ------------------------------------------------------------
                                                      p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧


  getFinalStoreᴸᴸ : ∀ {c' p c f f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → State
  getFinalStoreᴸᴸ {config σ _ _} m = σ

  &assoc : ∀ P Q R → P & Q & R ≡ (P & Q) & R
  &assoc [] Q R = refl
  &assoc (i :: is) Q R rewrite &assoc is Q R = refl

 
  stacklem1a : ∀ p q {pc a} → p ፦ pc ≡ just a → p ፦ pc ≡ (p & q) ፦ pc
  stacklem1a [] _ ()
  stacklem1a p [] _ rewrite &[] {p} = refl
  stacklem1a (p :: ps) q {+ 0} _ = refl
  stacklem1a (p :: ps) q {+ (suc n)} x = stacklem1a ps q x
  stacklem1a (p :: ps) q { -[1+ n ]} ()

  stacklem1b : ∀ p q {pc a} → p ፦ pc ≡ just a → (p & q) ፦ pc ≡ just a
  stacklem1b p q j rewrite (sym j) = sym (stacklem1a p q j)


  stacklem1c : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧
  stacklem1c {p} {q} (⊢LOADI prf) = ⊢LOADI (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢LOAD prf) = ⊢LOAD (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢ADD prf) = ⊢ADD (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢STORE prf) = ⊢STORE (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMP prf) = ⊢JMP (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMPLESStrue prf ltc) = ⊢JMPLESStrue (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPLESSfalse prf ltc) = ⊢JMPLESSfalse (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEtrue prf ltc) = ⊢JMPGEtrue (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEfalse prf ltc) = ⊢JMPGEfalse (stacklem1b p q prf) ltc

  stacklem1 : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  stacklem1 none = none
  stacklem1 (some one then) = some (stacklem1c one) (stacklem1 then)


  nothing≡pc : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → pc ≡ pc'
  nothing≡pc none = refl
  nothing≡pc (some (⊢LOADI ()) _)
  nothing≡pc (some (⊢LOAD ()) _)
  nothing≡pc (some (⊢ADD ()) _)
  nothing≡pc (some (⊢STORE ()) _)
  nothing≡pc (some (⊢JMP ()) _)
  nothing≡pc (some (⊢JMPLESStrue () _) _)
  nothing≡pc (some (⊢JMPGEtrue () _) _)
  nothing≡pc (some (⊢JMPLESSfalse () _) _)
  nothing≡pc (some (⊢JMPGEfalse () _) _)


  nothing≡s : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → s ≡ s'
  nothing≡s none = refl
  nothing≡s (some (⊢LOADI ()) _)
  nothing≡s (some (⊢LOAD ()) _)
  nothing≡s (some (⊢ADD ()) _)
  nothing≡s (some (⊢STORE ()) _)
  nothing≡s (some (⊢JMP ()) _)
  nothing≡s (some (⊢JMPLESStrue () _) _)
  nothing≡s (some (⊢JMPGEtrue () _) _)
  nothing≡s (some (⊢JMPLESSfalse () _) _)
  nothing≡s (some (⊢JMPGEfalse () _) _)

  nothing≡σ : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → σ ≡ σ'
  nothing≡σ none = refl
  nothing≡σ (some (⊢LOADI ()) _)
  nothing≡σ (some (⊢LOAD ()) _)
  nothing≡σ (some (⊢ADD ()) _)
  nothing≡σ (some (⊢STORE ()) _)
  nothing≡σ (some (⊢JMP ()) _)
  nothing≡σ (some (⊢JMPLESStrue () _) _)
  nothing≡σ (some (⊢JMPGEtrue () _) _)
  nothing≡σ (some (⊢JMPLESSfalse () _) _)
  nothing≡σ (some (⊢JMPGEfalse () _) _)

  nothing≡c : ∀ {c f c' f'} → [] ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → c ≡ c'
  nothing≡c none = refl
  nothing≡c (some (⊢LOADI ()) _)
  nothing≡c (some (⊢LOAD ()) _)
  nothing≡c (some (⊢ADD ()) _)
  nothing≡c (some (⊢STORE ()) _)
  nothing≡c (some (⊢JMP ()) _)
  nothing≡c (some (⊢JMPLESStrue () _) _)
  nothing≡c (some (⊢JMPGEtrue () _) _)
  nothing≡c (some (⊢JMPLESSfalse () _) _)
  nothing≡c (some (⊢JMPGEfalse () _) _)

  nothing≡f : ∀ {c f c' f'} → [] ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → f ≡ f'
  nothing≡f none = refl
  nothing≡f (some (⊢LOADI ()) _)
  nothing≡f (some (⊢LOAD ()) _)
  nothing≡f (some (⊢ADD ()) _)
  nothing≡f (some (⊢STORE ()) _)
  nothing≡f (some (⊢JMP ()) _)
  nothing≡f (some (⊢JMPLESStrue () _) _)
  nothing≡f (some (⊢JMPGEtrue () _) _)
  nothing≡f (some (⊢JMPLESSfalse () _) _)
  nothing≡f (some (⊢JMPGEfalse () _) _)

  stacklem2b : ∀ p q {pc i} → q ፦ pc ≡ just i → (p & q) ፦ (pc z+ size p) ≡ just i
  stacklem2b [] q {pc} prf rewrite sym (prf) | z+0 pc = refl
  stacklem2b (i :: is) q {+ 0} prf rewrite 0+z (size (i :: is)) = stacklem2b is q prf
  stacklem2b (i :: is) q {+ (suc n)} prf rewrite +comm n (suc (size` is)) | +comm (size` is) n = stacklem2b is q prf
  stacklem2b (i :: is) [] { -[1+ _ ]} ()
  stacklem2b (i :: is) (q :: qs) { -[1+ _ ]} ()
  
  stacklem2a : ∀ p q {σ s f pc' σ' s' f'} → q ⊢⟦ config σ s (+ 0) , f ⟧⇒⟦ config σ' s' pc' , f' ⟧ → (p & q) ⊢⟦ config σ s (size p) , f ⟧⇒⟦ config σ' s' (size p z+ pc') , f' ⟧
  stacklem2a p q (⊢LOADI x) rewrite +comm (size` p) 1 = ⊢LOADI (stacklem2b p q x)
  stacklem2a p q (⊢LOAD x) rewrite +comm (size` p) 1 = ⊢LOAD (stacklem2b p q x)
  stacklem2a p q (⊢STORE x) rewrite +comm (size` p) 1 = ⊢STORE (stacklem2b p q x)
  stacklem2a p q (⊢ADD x) rewrite +comm (size` p) 1 = ⊢ADD (stacklem2b p q x)
  stacklem2a p q (⊢JMP {offset = o} x) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMP (stacklem2b p q x)
  stacklem2a p q (⊢JMPLESSfalse x x₁) rewrite +comm (size` p) 1 = ⊢JMPLESSfalse (stacklem2b p q x) x₁
  stacklem2a p q (⊢JMPLESStrue {offset = o} x x₁) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMPLESStrue ((stacklem2b p q x)) x₁
  stacklem2a p q (⊢JMPGEtrue {offset = o} x x₁) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMPGEtrue ((stacklem2b p q x)) x₁
  stacklem2a p q (⊢JMPGEfalse x x₁) rewrite +comm (size` p) 1 = ⊢JMPGEfalse (stacklem2b p q x) x₁

{-
  stacklem2c : ∀ p i is {c c' f f'} → ((p & (i :: [])) & is) ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → (p & i :: is) ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ 
  stacklem2c = {!!}
-}
  stacklem2d : ∀ p n → size p z+ + suc n ≡ + suc ( size` p + n)
  stacklem2d [] n = refl
  stacklem2d (i :: is) n rewrite +comm (size` is) n | +comm (size` is) (suc n) = refl

{-
  stacklem2 : ∀ p q {σ s f pc' σ' s' f'} → q ⊢⟦ config σ s (+ 0) , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → (p & q) ⊢⟦ config σ s (size p) , f ⟧⇒*⟦ config σ' s' (size p z+ pc') , f' ⟧
  stacklem2 p [] q rewrite nothing≡σ q | nothing≡s q | sym (nothing≡pc q) | nothing≡f q | +comm (size` p) 0 = none
  stacklem2 p (x :: xs) none rewrite +comm (size` p) 0 = none
  stacklem2 p (x :: xs) (some {c = config σ s pc} {c' = config σ' s' (+ (suc n))} {c'' = config σ'' s'' pc''} {f} {f'} {f''} (one) rest) rewrite stacklem2d p n = some {c = config σ s (size p)} {c' = config σ' s' (size p z+ + (suc n)) }{c'' = config σ'' s'' (size p z+ pc'')} (stacklem2a p (x :: xs) one) (stacklem2c p x xs {!stacklem2a ? ? ?!})
  -}










{--
{--  &:: : ∀ {i is p'} → (i :: is) & p' ≡ i :: (is & p')
  &:: = refl
  
  redinst : ∀ i is n ub → inst (i :: is) (+ (suc n)) (+≤+ z≤n) (+≤+ (s≤s ub)) ≡ inst is (+ n) (+≤+ z≤n) (+≤+ ub)
  redinst i is n ub = refl --}

  addRightPC : ∀ {p q pc ub' lb} → (ub : pc < (size p) `ℤ`) → inst p pc lb ub ≡ inst (p & q) pc lb ub'
  addRightPC {[]} {q} {+ n} (+≤+ ())
  addRightPC {pc = negsuc n} {lb = ()}
  addRightPC {i :: is} {q} {+ 0} ub = refl
  addRightPC {i :: is} {q} {+ (suc n)} {+≤+ (s≤s ub')} (+≤+ (s≤s ub)) = addRightPC {is} {q} {+ n} (+≤+ ub)

  {--addRight : ∀ {p c c'} q → p ⊢ c ⇒ c' → (p & q) ⊢ c ⇒ c'
  addRight {p} [] rewrite &[] {p} = λ z → z
  addRight {p} (i :: []) = {!!}


  addRight* : ∀ {p c c'} q → p ⊢ c ⇒* c' → (p & q) ⊢ c ⇒* c'
  addRight* q (none p) = none p
  addRight* q (some one rest) = {!!}--}


  p<+ : ∀ {q y p} → (+ 0) ≤ (size q) `ℤ` → y < (size p) `ℤ` → y < (size (p & q)) `ℤ`
  p<+ {q} {y} {p} (+≤+ z≤n) ub rewrite size&+ p q = ℤ<+s {+ (size` q)} {y} {+ (size` p)} (+≤+ z≤n) ub

  i≡p : ∀ p q pc lb ub ub' i → i ≡ inst p pc lb ub → i ≡ inst (p & q) pc lb ub'
  i≡p p q pc lb ub ub' i prf rewrite prf = addRightPC {p} {q} {pc} {ub'} {lb} ub

  add⊢Right :  ∀ {p q c c'} → p ⊢ c ⇒ c' → (p & q) ⊢ c ⇒ c'
  add⊢Right {p} {[]} rewrite &[] {p} = λ z → z
  add⊢Right {p} {q} (exec1 {p} {c} i lb ub {ieq} {vh}) = exec1 i lb (p<+ (+≤+ z≤n) ub) {i≡p p q (pc c) lb ub (p<+ (+≤+ z≤n) ub) i ieq} {vh}

  add⊢Right* : ∀ {p q c c'} → p ⊢ c ⇒* c' → (p & q) ⊢ c ⇒* c'
  add⊢Right* 0r = 0r
  add⊢Right* (step one then) = step (add⊢Right one) (add⊢Right* then) 























-------------
{--
  data ExeStep (p : Prog)(c : Config)(c' : Config) : Set where
    step : {i : Inst}{l1 : Lem1 i (height (stack c))}{l2 : Lem2 (pc c) p}{defi : i ≡ inst p (pc c) {l2}}{defc' : c' ≡ iexe i c l1 } → ExeStep p c c'

  data Step {A : Set}(r : A → A)(x : A) : A → Set where
    stp : Step r x (r x)
  
  data Star {A : Set}(r : A → A) : A → A → Set where
    none : {x : A} → Star r x x
    some : {x y z : A} → Step r x y → Star r y z → Star r x z

  
  data ⦅_,_⦆↦_ : Prog → Config → Config → Set where
    base : ∀ {p c}{ivpc : (size p) ≤ (pc c) `ℤ`} → ⦅ p , c ⦆↦ c
    trans : ∀ {p c c' c''} → ExeStep p c c' → ⦅ p , c' ⦆↦ c'' → ⦅ p , c ⦆↦ c''

--}
--}
