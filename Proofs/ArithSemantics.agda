module Proofs.ArithSemantics where

  open import Proofs.NatProofs
  open import Proofs.Stack

  open import Semantics.LowLevel

  open import Lang.Expr
  open import Lang.Stack

  open import Compiler

  open import Data.Nat renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (_+_ to _ℤ+_; suc to zuc) hiding (_≟_)
  open import Data.Maybe using (just)

  open import Base.DataStructures
  open import Misc.Base

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  
------------------------------------------------------
-- Proofs for semantics over arithmetic expressions --
------------------------------------------------------

  -- Given an arithmetic expression 'a' we can produce the semantics of executing 'a' compiled into the SML.
  Lemma1a : ∀ a {σ s f} → (acomp a) ⊢⟦ config σ s (+ 0) , (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config σ (aexe a σ , s) (+ size` (acomp a)) , f ⟧
  Lemma1a (NAT n) = some (⊢LOADI refl) none
  Lemma1a (VAR x) = some (⊢LOAD refl) none
  Lemma1a (m + n) {σ} {s} {f} with Lemma1a m {σ} {s} {f} | Lemma1a n {σ} {aexe m σ , s} {f}
  ... | msem | nsem with stacklem1 {q = acomp n & ADD :: []} msem | stacklem2 (acomp m) _ (stacklem1 {q = ADD :: []} nsem) | stacklem2c (acomp m & acomp n) ADD []
  ... | msem' | nsem' | addprf
  
      rewrite size`&+ {acomp m} {acomp n & ADD :: []} | size`&+ {acomp n} {ADD :: []} | +comm (size` (acomp m)) (size` (acomp n) ℕ+ 1) | sym (+assoc (size` (acomp n) ℕ+ 1) (size` (acomp m)) f) | +comm (size` (acomp n)) 1 | +comm (aexe m σ) (aexe n σ) | size`&+ {acomp m} {acomp n} | +comm (size` (acomp m)) (size` (acomp n)) | &assoc (acomp m) (acomp n) (ADD :: [])
      
      = TransComp* (addF*' (suc (size` (acomp n))) msem') (TransComp (addF*' 1 nsem') (⊢ADD addprf))


  -- Lemma 1. Given a command 'x := a' compiled into SML, and an initial computational state with enough fuel to complete execution,
  -- we can produce the semantics of this execution, where the final store is the 'x := ``evaluation of a`` ' pushed on to the initial store.
  Lemma1 : ∀ {a σ f x s} → compile (x ≔ a) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config ((x ≔ (aexe a σ)) ∷ σ) s (+ suc (size` (acomp a))) , f ⟧
  Lemma1 {a} {σ} {f} {s = s} with Lemma1a a {σ} {s} {suc f}
  ... | z rewrite +swap {size` (acomp a)} {f} = TransComp (stacklem1 {q = STORE _ :: []} z) (⊢STORE (stacklem2c (acomp a) (STORE _) []))


  -------------------------------------------------------------------------------------------------------------------------------------------
  -- The following proofs use the above proofs and program composition to generate semantics where there is additional instructions before --
  -- and/or after the arithmetic expression. They are not necessary proofs, but remove some of the steps from proofs in other modules.     --
  -------------------------------------------------------------------------------------------------------------------------------------------

  -- We can add instructions after arithmetic expressions.
  Lemma1' : ∀ {a rest σ s f} → ((acomp a) & rest) ⊢⟦ config σ s (+ 0) , size` (acomp a & rest) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , size` rest ℕ+ f ⟧
  Lemma1' {a} {rest} {f = f} rewrite size`&+ {acomp a} {rest} | sym (+assoc (size` (acomp a)) (size` rest) (f)) = stacklem1 (Lemma1a a)

  -- As above but excluding the extra added fuel.
  Lemma1'' : ∀ {a rest σ s f} → ((acomp a) & rest) ⊢⟦ config σ s (+ 0) , size` (acomp a) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a)) , f ⟧
  Lemma1'' {a} = stacklem1 (Lemma1a a)

  -- As above but including the store instruction.
  Lemma1''&Store : ∀ {a x rest σ s f} → (acomp a & STORE x :: rest) ⊢⟦ config σ s (+ 0) , suc (size` (acomp a) ℕ+ f) ⟧⇒*⟦ config ((x ≔ (aexe a σ)) ∷ σ) s (+ suc (size` (acomp a))) , f ⟧
  Lemma1''&Store {a} {x} {rest} {σ} {s} {f} with Lemma1a a {σ} {s} {suc f}
  ... | z rewrite +comm (size` (acomp a)) (suc f) | +comm f (size` (acomp a)) with stacklem1 {q = STORE x :: rest} z
  ... | z' = TransComp z' (⊢STORE (stacklem2c (acomp a) (STORE x) rest))

  -- We can add instructions both before and after the execution of arithmetic expressions.
  ArithExec : ∀ {a this that σ s f} → (this & (acomp a) & that) ⊢⟦ config σ s (size this) , size` (acomp a) ℕ+ f ⟧⇒*⟦ config σ (aexe a σ , s) (size (acomp a & this)) , f ⟧
  ArithExec {a} {this} {that} {σ} {s} {f} with Lemma1a a {σ} {s} {f}
  ... | asem with stacklem1 {q = that} asem
  ... | asem' with stacklem2 (this) _ asem'
  ... | asem'' rewrite size`&+ {acomp a} {this} = asem''

  -- Given enough fuel then the final program counter will be equal to the size of the arithmetic expression + 1 for the store instruction.
  ArithFullExec : ∀ {n x σ f pc'} → (acomp n & STORE x :: []) ⊢⟦ config σ $ (+ 0) , suc (size` (acomp n) ℕ+ suc f) ⟧⇒*⟦ config ((x ≔ aexe n σ) ∷ σ) $ pc' , suc f ⟧ → pc' ≡ size (acomp n & STORE x :: [])
  ArithFullExec {n} {x} sem rewrite size`&+ {acomp n} {STORE x :: []} | +comm (size` (acomp n)) 1 = deterministic-pc (Lemma1 {n}) sem

  

