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
  open import Proofs.Basic
  open import Proofs.NatProofs


  data _⊢_⇒_ : Prog → Config → Config → Set where
    exec1 : ∀ {p c} → (i : Inst)(lb : (pos 0) ≤ (pc c) `ℤ`)(ub : (pc c)  < (size p) `ℤ`){ieq : i ≡ (inst p (pc c) lb ub)}{vh : Lem1 i (height (stack c))} → p ⊢ c ⇒ iexe i c vh

  data _⊢_⇒*_ : Prog → Config → Config → Set where
    0r   : ∀ {p c} → p ⊢ c ⇒* c
    step : ∀ {p c c' c''} → p ⊢ c ⇒ c' → p ⊢ c' ⇒* c'' → p ⊢ c ⇒* c''

  data _×_⇒_  : Prog → Config → Config → Set where
  
    ×LOADI        : ∀ {p state stack pc n}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ LOADI n}
                    ------------------------------------------------------------------------
                       → p × config state stack pc ⇒ config state (n , stack) (zuc pc)


    ×LOAD         :      ∀ {p state stack pc v}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ LOAD v}
                    ---------------------------------------------------------------------------------
                    → p × config state stack pc ⇒ config state ((get-var v state) , stack) (zuc pc)


    ×STORE        :   ∀ {p state rest n pc v}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ STORE v}
                    -----------------------------------------------------------------------------
                    → p × config state (n , rest) pc ⇒ config (set-var v n state) rest (zuc pc)


    ×ADD          :       ∀ {p state rest n1 n2 pc}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ ADD}
                    -----------------------------------------------------------------------------------
                    → p × config state (n1 , n2 , rest) pc ⇒ config state ((n1 + n2) , rest) (zuc pc)


    ×JMP          : ∀ {p state stack pc z}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ JMP z}
                    ----------------------------------------------------------------------
                       → p × config state stack pc ⇒ config state stack (zuc pc z+ z)


    ×JMPLESStrue  : ∀ {p state rest head next pc z}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ JMPLESS z}{ineq : head ≤ next}
                    -------------------------------------------------------------------------------------------------------
                                → p × config state (head , next , rest) pc ⇒ config state rest (zuc pc)


    ×JMPLESSfalse : ∀ {p state rest head next pc z}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ JMPLESS z}{ineq : head > next}
                   --------------------------------------------------------------------------------------------------------
                               → p × config state (head , next , rest) pc ⇒ config state rest (zuc pc z+ z)


    ×JMPGEtrue    : ∀ {p state rest head next pc z}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ JMPGE z}{ineq : head ≤ next}
                   ------------------------------------------------------------------------------------------------------
                              → p × config state (head , next , rest) pc ⇒ config state rest (zuc pc z+ z)


    ×JMPGEfalse   : ∀ {p state rest head next pc z}(lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size p) `ℤ`){eqi : inst p pc lb ub ≡ JMPGE z}{ineq : head > next}
                   ------------------------------------------------------------------------------------------------------
                              → p × config state (head , next , rest) pc ⇒ config state rest (zuc pc)

  data _×_⇒*_ : Prog → Config → Config → Set where

    none : ∀ {p c} →  
                       -----------------
                         p × c ⇒* c


    some : ∀ {p c c' c''} →   p × c ⇒ c' → p × c' ⇒* c'' →
                              ---------------------------------
                                       p × c ⇒* c''

{--  &:: : ∀ {i is p'} → (i :: is) & p' ≡ i :: (is & p')
  &:: = refl
  
  redinst : ∀ i is n ub → inst (i :: is) (pos (suc n)) (+≤+ z≤n) (+≤+ (s≤s ub)) ≡ inst is (pos n) (+≤+ z≤n) (+≤+ ub)
  redinst i is n ub = refl --}

  addRightPC : ∀ {p q pc ub' lb} → (ub : pc < (size p) `ℤ`) → inst p pc lb ub ≡ inst (p & q) pc lb ub'
  addRightPC {[]} {q} {pos n} (+≤+ ())
  addRightPC {pc = negsuc n} {lb = ()}
  addRightPC {i :: is} {q} {pos 0} ub = refl
  addRightPC {i :: is} {q} {pos (suc n)} {+≤+ (s≤s ub')} (+≤+ (s≤s ub)) = addRightPC {is} {q} {pos n} (+≤+ ub)

 {-- addRight : ∀ {p q c c'} → p × c ⇒ c' → (p & q) × c ⇒ c'
  addRight {p} {[]} rewrite &[] {p} = λ z → z
  addRight {p} {i :: is} = {!!}


  addRight* : ∀ {p q c c'} → p × c ⇒* c' → (p & q) × c ⇒* c'
  addRight* none = none
  addRight* (some one rest) = some (addRight one) (addRight* rest) --}


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
