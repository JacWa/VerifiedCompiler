module Proofs.BExpSemantics where

  open import Semantics.HighLevel  
  open import Semantics.LowLevel

  open import Agda.Builtin.Sigma renaming (_,_ to _∣_)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat using (_<_)


  open import Data.Bool using (_≟_)
  open import Data.Nat using (suc; _≤?_) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties
  open import Data.Integer using (+_) renaming (_+_ to _z+_; suc to zuc)
  open import Data.Empty

  open import Lang.Expr renaming (_≟_ to _≟ⁱ_)
  open import Lang.Stack
  open import Compiler

  open import Base.DataStructures
  open import Base.Existential
  open import Base.Tuple renaming (_,_ to _~_)

  open import Proofs.ArithSemantics
  open import Proofs.Basic
  open import Proofs.Fuel
  open import Proofs.NatProofs
  open import Proofs.Stack
  open import Proofs.Bool
  
  open import Relation.Nullary

  open import Misc.Base
  
  mutual
    Lemma2 : ∀ b Q {f s σ} → bexe b σ ≡ false → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b false σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q) & Q)) , f ⟧
    Lemma2 (BOOL x) y z rewrite z = some (⊢JMP refl) none
    Lemma2 (NOT x) y z = Lemma2' x y (notfalse z)
    Lemma2 (a AND b) y {f} {s} {σ} z rewrite sym (&assoc (bcomp a false (+ (size` (bcomp b false (size y)) ℕ+ size` y))) (bcomp b false (size y)) y) with bexe a σ ≟ false
    ... | yes prf rewrite sym (size`&+ {bcomp b false (+ size` y)} {y}) | size`&+ {bcomp a false (+ size` (bcomp b false (+ size` y) & y))} {bcomp b false (+ size` y)} | sym (+assoc (size` (bcomp a false (+ size` (bcomp b false (+ size` y) & y)))) (size` (bcomp b false (+ size` y))) f) | prf | sym (size`&+ {bcomp b false (+ size` y)} {y}) = Lemma2 a (bcomp b false (+ size` y) & y) prf
    ... | no prf with ∧-false prf z | ¬-false prf
    ... | w | w' rewrite w' with Lemma3 a (bcomp b false (+ size` y) & y) {(fuelLLb b false σ (+ size` y) ℕ+ f)} {s} {σ} w'
    ... | w'' rewrite sym (+assoc (fuelLLb a false σ (+ (size` (bcomp b false (+ size` y)) ℕ+ size` y))) (fuelLLb b false σ (size y)) f) | size`&+ {bcomp b false (+ size` y)} {y} with bcomp a false (+ (size` (bcomp b false (+ size` y)) ℕ+ size` y))
    ... | A rewrite size`&+ {A} {bcomp b false (+ size` y) & y} | +comm (size` A) (size` (bcomp b false (+ size` y) & y)) = insertAtEnd* w'' (stacklem2 A (bcomp b false (+ size` y) & y) (Lemma2 b y w))
    Lemma2 (a LT b) y {f} {s} {σ} z rewrite sym (&assoc (acomp a) (acomp b & JMPGE (size y) :: []) y) | sym (&assoc (acomp b) (JMPGE (size y) :: []) y) | size`&+ {acomp a} {acomp b & JMPGE (+ size` y) :: []} | sym (+assoc (size` (acomp a)) (size` (acomp b & JMPGE (+ size` y) :: [])) f) with ArithExec {a} {[]} {acomp b & JMPGE (+ size` y) :: y} {σ} {s} {(size` (acomp b) ℕ+ 1) ℕ+ f}
    ... | w rewrite +assoc (size` (acomp a)) (size` (acomp b) ℕ+ 1) f | sym (size`&+ {acomp b} {JMPGE (+ size` y) :: []}) = insertAtEnd* w (insertAtEnd (Lemma2Aux1 {a} {b}) (Lemma2Aux2 {a} {b}))


    Lemma2' : ∀ b Q {f s σ} → bexe b σ ≡ true → (bcomp b true (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b true σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b true (size Q) & Q)) , f ⟧
    Lemma2' (BOOL x) y z rewrite z = some (⊢JMP refl) none
    Lemma2' (NOT x) y z = Lemma2 x y (nottrue z)
    Lemma2' (a AND b) y {f} {s} {σ} z with bexe a σ ≟ true
    ... | no prf = ⊥-elim (∧-true prf z)
    ... | yes prf rewrite prf | sym (+assoc (fuelLLb a false σ (+ size` (bcomp b true (+ size` y)))) (fuelLLb b true σ (+ size` y)) f) with Lemma2' b y {f} {s} {σ} z
    ... | w = insertAtEnd* (stacklem1 (Lemma3 a (bcomp b true (+ size` y)) prf)) (Lemma2'Aux1 {a} {b} {y} (stacklem2 (bcomp a false (+ size` (bcomp b true (+ size` y)))) ((bcomp b true (+ size` y)) & y) {pc = + 0} w))
    Lemma2' (a LT b) y {f} {s} {σ} z with stacklem1 {q = y} (Lemma1' {a} {acomp b & JMPLESS (size y) :: []} {σ} {s} {f})
    ... | w rewrite sym (&assoc (acomp a) (acomp b & JMPLESS (+ size` y) :: []) (y)) | sym (&assoc (acomp b) (JMPLESS (+ size` y) :: []) y) | sym (size`&+ {acomp b} {JMPLESS (+ size` y) :: []}) | sym (size`&+ {acomp a} {acomp b & JMPLESS (+ size` y) :: []}) with ArithExec {b} {acomp a} {JMPLESS (+ size` y) :: y} {σ} {aexe a σ , s} {suc f}
    ... | w' rewrite size`&+ {acomp b} {JMPLESS (+ size` y) :: []} | sym (+assoc (size` (acomp b)) 1 f) = insertAtEnd* w (insertAtEnd w' (Lemma2'Aux2 {a} {b} z))
    
    Lemma2'Aux1 : ∀ {a b y σ s f} → ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y) & y) ⊢⟦ config σ s (+ size` (bcomp a false (+ size` (bcomp b true (+ size` y))))) , fuelLLb b true σ (+ size` y) ℕ+ f ⟧⇒*⟦ config σ s (+ (size` (bcomp b true (+ size` y) & y) ℕ+ size` (bcomp a false (+ size` (bcomp b true (+ size` y)))))) , f ⟧) → ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y)) & y) ⊢⟦ config σ s (size (bcomp a false (size (bcomp b true (+ size` y))))) , fuelLLb b true σ (+ size` y) ℕ+ f ⟧⇒*⟦ config σ s (+ size` ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y)) & y)) , f ⟧
    Lemma2'Aux1 {a} {b} {y} {σ} {s} {f} sem with bcomp b true (+ size` y)
    ... | B with (bcomp a false (+ size` B))
    ... | A rewrite +comm (size` (B & y)) (size` A) | sym (size`&+ {A} {B & y}) | &assoc A B y = sem

    Lemma2'Aux2 : ∀ {a} {b} {y} {σ} {s} {f} → (aexe a σ < aexe b σ) ≡ true → (acomp a & acomp b & JMPLESS (+ size` y) :: y) ⊢⟦ config σ (aexe b σ , aexe a σ , s) (+ size` (acomp b & acomp a)) , suc f ⟧⇒⟦ config σ s (+ size` (acomp a & acomp b & JMPLESS (+ size` y) :: y)) , f ⟧
    Lemma2'Aux2 {a} {b} {y} {σ} {s} {f} z with stacklem2c (acomp a & acomp b) (JMPLESS (size y)) y
    ... | w rewrite &assoc (acomp a) (acomp b) (JMPLESS (size y) :: y) | size`trans (acomp a) (acomp b) with ⊢JMPLESStrue {((acomp a & acomp b) & JMPLESS (+ size` y) :: y)} {σ} {s} {aexe b σ} {aexe a σ} {(size` (acomp b & acomp a))} {size y} {f} w (<-true z)
    ... | w' rewrite sym (&assoc (acomp a) (acomp b) (JMPLESS (+ size` y) :: y)) | size`&+3/4 (acomp a) (acomp b) (JMPLESS (+ size` y) :: []) y | &assoc (acomp a) (acomp b) y | size`&+ {acomp a & acomp b} {y} | size`trans (acomp a) (acomp b) = w'
    
    postulate
      Lemma2Aux1 : ∀ {a} {b} {y} {σ} {s} {f} → (acomp a & acomp b & JMPGE (+ size` y) :: y) ⊢⟦ config σ (aexe a σ , s) (size (acomp a & [])) , size` (acomp b & JMPGE (+ size` y) :: []) ℕ+ f ⟧⇒*⟦ config σ (aexe b σ , aexe a σ , s) (size (acomp a & acomp b)) , size` (JMPGE (+ size` y) :: []) ℕ+ f ⟧
      Lemma2Aux2 : ∀ {a} {b} {y} {σ} {s} {f} → (acomp a & acomp b & JMPGE (+ size` y) :: y) ⊢⟦ config σ (aexe b σ , aexe a σ , s) (size (acomp a & acomp b)) , size` (JMPGE (+ size` y) :: []) ℕ+ f ⟧⇒⟦ config σ s (+ size` (acomp a & acomp b & JMPGE (+ size` y) :: y)) , f ⟧
      Lemma3 : ∀ b Q {f s σ} → bexe b σ ≡ true  → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b false σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q))) , f ⟧
  postulate
    Lemma4 : ∀ {c} {b} {σ} → bexe b σ ≡ false → size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ≡ fuelLLb b false σ ((size (compile c)) z+ (+ 1))
