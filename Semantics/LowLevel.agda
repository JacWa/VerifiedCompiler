module Semantics.LowLevel where

  open import Lang.Stack
  open import Base.DataStructures
  open import Data.Nat using (ℕ; suc; _+_; _≤_; _>_)
  open import Data.Integer using (+_) renaming (_+_ to _z+_)
  open import Data.Maybe using (just; nothing)
  open import Agda.Builtin.Equality

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
