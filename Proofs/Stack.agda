module Proofs.Stack where

  open import Lang.Stack
  open import Base.DataStructures
  open import Data.Bool
  open import Misc.Base
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.Star
  open import Data.Nat.Base
  open import Data.Maybe
  open import Proofs.Basic
  open import Proofs.NatProofs
  open import Relation.Binary

{--
  data _⊢_⇒_ : Prog → Config → Config → Set where
    exec1 : ∀ {p c} → (i : Inst)(lb : (pos 0) ≤ (pc c) `ℤ`)(ub : (pc c)  < (size p) `ℤ`){ieq : i ≡ (inst p (pc c) lb ub)}{vh : Lem1 i (height (stack c))} → p ⊢ c ⇒ iexe i c vh

  data _⊢_⇒*_ : Prog → Config → Config → Set where
    0r   : ∀ {p c} → p ⊢ c ⇒* c
    step : ∀ {p c c' c''} → p ⊢ c ⇒ c' → p ⊢ c' ⇒* c'' → p ⊢ c ⇒* c''
--}
  data _×_⇒_ : Prog → Config → Config → Set where
  
    ×LOADI        :        ∀ {p state stack pc n} → (p ፦ (pos pc)) ≡ just (LOADI n)
                    ------------------------------------------------------------------------------
                     → p × config state stack (pos pc) ⇒ config state (n , stack) (pos (suc pc))


    ×LOAD         :        ∀ {p state stack pc x} → (p ፦ (pos pc)) ≡ just (LOAD x)
                    ---------------------------------------------------------------------------------------------
                    → p × config state stack (pos pc) ⇒ config state ((get-var x state) , stack) (pos (suc pc))


    ×STORE        :          ∀ {p state n rest pc x} → (p ፦ (pos pc)) ≡ just (STORE x)
                    ----------------------------------------------------------------------------------------
                    → p × config state (n , rest) (pos pc) ⇒ config ((x ≔ n) ∷ state) rest (pos (suc pc))


    ×ADD          :            ∀ {p state rest n1 n2 pc} → (p ፦ (pos pc)) ≡ just ADD
                    -----------------------------------------------------------------------------------------------
                    → p × config state (n1 , n2 , rest) (pos pc) ⇒ config state ((n1 + n2) , rest) (pos (suc pc))


    ×JMP          :            ∀ {p state stack pc offset} → (p ፦ (pos pc)) ≡ just (JMP offset)
                    -------------------------------------------------------------------------------------
                       → p × config state stack (pos pc) ⇒ config state stack (pos (suc pc) z+ offset)


    ×JMPLESSfalse : ∀ {p state rest head next pc offset} → (p ፦ (pos pc)) ≡ just (JMPLESS offset) → head ≤ next
                    ----------------------------------------------------------------------------------------------
                        → p × config state (head , next , rest) (pos pc) ⇒ config state rest (pos (suc pc))


    ×JMPLESStrue :  ∀ {p state rest head next pc offset} → (p ፦ (pos pc)) ≡ just (JMPLESS offset) → head > next
                   -----------------------------------------------------------------------------------------------
                   → p × config state (head , next , rest) (pos pc) ⇒ config state rest (pos (suc pc) z+ offset)


    ×JMPGEtrue    : ∀ {p state rest head next pc offset} → (p ፦ (pos pc)) ≡ just (JMPGE offset) → head ≤ next
                   ------------------------------------------------------------------------------------------------
                   → p × config state (head , next , rest) (pos pc) ⇒ config state rest (pos (suc pc) z+ offset)


    ×JMPGEfalse   : ∀ {p state rest head next pc offset} → (p ፦ (pos pc)) ≡ just (JMPGE offset) → head > next
                   ---------------------------------------------------------------------------------------------
                     → p × config state (head , next , rest) (pos pc) ⇒ config state rest (pos (suc pc))

  data _×_⇒*_ : Prog → Config → Config → Set where

    none : ∀ {p σ s pc}-- pc'} →                       pc ≡ pc'
                               --------------------------------------------
                                → p × (config σ s pc) ⇒* (config σ s pc)


    some : ∀ {p c c' c''} →   p × c ⇒ c' → p × c' ⇒* c'' →
                              ---------------------------------
                                       p × c ⇒* c''


  data _⊢_⇒_ : Prog → Config → Config → Set where
  
    exec1 : ∀ {p state stack pc} → (i : Inst) → p ፦ pc ≡ just i → {vh : Lem1 i (height stack)}
            ------------------------------------------------------------------------------------
                    → p ⊢ (config state stack pc) ⇒ iexe i (config state stack pc) vh

  data _⊢_⇒*_ : Prog → Config → Config → Set where
    0r   : ∀ {p c} → p ⊢ c ⇒* c
    step : ∀ {p c c' c''} → p ⊢ c ⇒ c' → p ⊢ c' ⇒* c'' → p ⊢ c ⇒* c''


  stacklem1a : ∀ p q {pc a} → p ፦ pc ≡ just a → p ፦ pc ≡ (p & q) ፦ pc
  stacklem1a [] _ ()
  stacklem1a p [] _ rewrite &[] {p} = refl
  stacklem1a (p :: ps) q {pos 0} _ = refl
  stacklem1a (p :: ps) q {pos (suc n)} x = stacklem1a ps q x
  stacklem1a (p :: ps) q {negsuc n} ()

  stacklem1b : ∀ p q {pc a} → p ፦ pc ≡ just a → (p & q) ፦ pc ≡ just a
  stacklem1b p q j rewrite (sym j) = sym (stacklem1a p q j)

  stacklem1c : ∀ {p q c c'} → p ⊢ c ⇒ c' → (p & q) ⊢ c ⇒ c'
  stacklem1c {p} {q} (exec1 i a) = exec1 i (stacklem1b p q a)

  stacklem1 : ∀ {p q c c'} → p ⊢ c ⇒* c' → (p & q) ⊢ c ⇒* c'
  stacklem1 0r = 0r
  stacklem1 (step one then) = step (stacklem1c one) (stacklem1 then)
{--
  stacklem2 : ∀ {p q σ σ' s s' pc pc'} → p ⊢ (config σ s pc) ⇒* (config σ' s' pc') → (q & p) ⊢ (config σ s (pc z+ (size q))) ⇒* (config σ' s' (pc' z+ (size q)))
  stacklem2 = {!!}

  compexec : ∀ {p q σ σ' σ'' s s' s'' pc' pc''} → p ⊢ (config σ s (pos 0)) ⇒ (config σ' s' pc') → size p ≡ pc' → p ⊢ (config σ' s' (pc' z- (size p))) ⇒ (config σ'' s'' pc'') →(p & q) ⊢ (config σ s (pos 0)) ⇒ (config σ'' s'' ((size p) z+ pc''))
  compexec = {!!}

  --}









{--
{--  &:: : ∀ {i is p'} → (i :: is) & p' ≡ i :: (is & p')
  &:: = refl
  
  redinst : ∀ i is n ub → inst (i :: is) (pos (suc n)) (+≤+ z≤n) (+≤+ (s≤s ub)) ≡ inst is (pos n) (+≤+ z≤n) (+≤+ ub)
  redinst i is n ub = refl --}

  addRightPC : ∀ {p q pc ub' lb} → (ub : pc < (size p) `ℤ`) → inst p pc lb ub ≡ inst (p & q) pc lb ub'
  addRightPC {[]} {q} {pos n} (+≤+ ())
  addRightPC {pc = negsuc n} {lb = ()}
  addRightPC {i :: is} {q} {pos 0} ub = refl
  addRightPC {i :: is} {q} {pos (suc n)} {+≤+ (s≤s ub')} (+≤+ (s≤s ub)) = addRightPC {is} {q} {pos n} (+≤+ ub)

  {--addRight : ∀ {p c c'} q → p × c ⇒ c' → (p & q) × c ⇒ c'
  addRight {p} [] rewrite &[] {p} = λ z → z
  addRight {p} (i :: []) = {!!}


  addRight* : ∀ {p c c'} q → p × c ⇒* c' → (p & q) × c ⇒* c'
  addRight* q (none p) = none p
  addRight* q (some one rest) = {!!}--}


  p<+ : ∀ {q y p} → (pos 0) ≤ (size q) `ℤ` → y < (size p) `ℤ` → y < (size (p & q)) `ℤ`
  p<+ {q} {y} {p} (+≤+ z≤n) ub rewrite size&+ p q = ℤ<+s {pos (size` q)} {y} {pos (size` p)} (+≤+ z≤n) ub

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
