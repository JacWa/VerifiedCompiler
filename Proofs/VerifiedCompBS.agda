module Proofs.VerifiedCompBS where

  open import Semantics.HighLevel  
  open import Semantics.LowLevel

  open import Agda.Builtin.Sigma renaming (_,_ to _∣_)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool


  open import Data.Nat using (suc; _≤?_) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using ()
  open import Data.Integer using (+_) renaming (_+_ to _z+_; suc to zuc)
  open import Data.Integer.Properties using (n⊖n≡0)
  open import Data.Empty

  open import Lang.Expr
  open import Lang.Stack
  open import Compiler

  open import Base.DataStructures
  open import Base.Existential
  open import Base.Tuple renaming (_,_ to _~_)

  open import Proofs.ArithSemantics
  open import Proofs.BExpSemantics
  open import Proofs.Basic
  open import Proofs.BigStepHL
  open import Proofs.Fuel
  open import Proofs.NatProofs
  open import Proofs.Stack
  
  open import Relation.Nullary

  open import Misc.Base using (neg)


  postulate
    Lemma'-helper : ∀ {I σ σ' f f' pc'}  (semhl : ⟦ I , σ , suc f ⟧⇛⟦ σ' , suc f' ⟧)→ compile I ⊢⟦ config σ $ (+ 0) , fuelLLBS' semhl ℕ+ suc f' ⟧⇒*⟦ config σ' $ pc' , suc f' ⟧ → pc' ≡ size (compile I)

  Lemma' : ∀ {I σ f f' σ' } → (semhl : ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧) → ∃[ pc' ] (compile I ⊢⟦ config σ $ (+ 0) , fuelLLBS semhl ⟧⇒*⟦ config σ' $ pc' , f' ⟧)

  -- Case where the initial fuel (f) is 0.
  Lemma' Empty = _ ∣ none

  -- Skip case.
  Lemma' Skip  = _ ∣ none

  -- Assignment case.
  Lemma' {_ ≔ a} Assign = _ ∣ makeArithSem {a}
  
  -- Sequential composition case where fuel runs out when executing first expression
  Lemma' {_ ⋯ I'} (Seq {f' = 0} semhl Empty) with Lemma' semhl
  ... | pc' ∣ semll rewrite +0 ((fuelLLBS' semhl) ℕ+ 0) = pc' ∣ stacklem1 {q = compile I'} semll

  -- Sequential composition case where there is enough fuel to execute at least first expression.
  Lemma' {I ⋯ I'} {σ} (Seq {s' = σ'}{f = f}{suc f'}{f''} semhl semhl') with Lemma' semhl | Lemma' semhl'
  ... | pc' ∣ semll | pc'' ∣ semll' with suc f' ≤? (fuelLLBS' semhl' ℕ+ f'')
  ... | yes p with NatLem2 (suc f') (fuelLLBS' semhl' ℕ+ f'') p
  ... | ε ∣ z with stacklem1 {q = compile I'} semll
  ... | semll* rewrite sym (+assoc (fuelLLBS' semhl) (fuelLLBS' semhl') f'') | sym z | +assoc (fuelLLBS' semhl) f' ε with Lemma'-helper semhl semll | stacklem2 (compile I) (compile I') semll'
  ... | prf | semll'* rewrite sym prf = pc'' z+ pc' ∣ insertAtEnd* (helper) semll'* 
    where
    helper : (compile I & compile I') ⊢⟦ config σ $ (+ 0) , fuelLLBS' semhl ℕ+ suc (f' ℕ+ ε) ⟧⇒*⟦ config σ' $ pc' , suc (f' ℕ+ ε) ⟧
    helper rewrite +assoc (fuelLLBS' semhl) (suc f') ε = addF* ε semll*

  -- Sequential composition case where there is enough fuel to execute at least the first expression, but the second expression requires less fuel when compiled to LL than in HL. This could possibly be joined with the above case, but is seperate for ease of proof.
  Lemma' {I ⋯ I'} (Seq {f = f}{suc f'}{f''} semhl semhl') | pc' ∣ semll | pc'' ∣ semll' | no ¬p rewrite +comm (fuelLLBS' semhl) (suc f') | +comm f' (fuelLLBS' semhl) | sym (+0 (suc f')) | +comm (fuelLLBS' semhl) f' with addF* (fuelLLBS' semhl' ℕ+ f'') (stacklem1 {q = compile I'} (subF* {f' = 0} (suc f') semll))
  ... | semll* rewrite +assoc (fuelLLBS' semhl) (fuelLLBS' semhl') f'' with stacklem2 (compile I) _ semll'
  ... | semll'* rewrite +comm (suc f') (fuelLLBS' semhl) | +0 f' | Lemma'-helper semhl semll = pc'' z+ + size` (compile I) ∣ (insertAtEnd* (semll*) semll'*)

  --IfFalse case
  Lemma' {IF b THEN P ELSE Q} {σ} {f' = f'} (IfFalse x semhl) rewrite x with stacklem1 {q = compile Q} (Lemma2 b (compile P & JMP (+ size` (compile Q)) :: []) {fuelLLBS' semhl ℕ+ f'} {$} {σ} x) 
  ... | semll rewrite size`&+ {compile P} {JMP (+ size` (compile Q)) :: []} | +assoc (fuelLLb b false σ (+ (size` (compile P) ℕ+ 1))) (fuelLLBS' semhl) f' with Lemma' semhl
  ... | pc'' ∣ semll' with stacklem2 (bcomp b false (+ (size` (compile P) ℕ+ 1)) & compile P & JMP (+ size` (compile Q)) :: []) _ semll'
  ... | semll'* = pc'' z+ + size` (bcomp b false (+ (size` (compile P) ℕ+ 1)) & compile P & JMP (+ size` (compile Q)) :: []) ∣ (insertAtEnd* semll semll'*)

  --IfTrue case.
  Lemma' {IF b THEN P ELSE Q} {σ} {f' = f'} (IfTrue x semhl) rewrite x with stacklem1 {q = compile Q} (Lemma3 b (compile P & JMP (+ size` (compile Q)) :: []) {fuelLLBS' semhl ℕ+ f'} {$} {σ} x)
  ... | semll rewrite size`&+ {compile P} {JMP (+ size` (compile Q)) :: []} | +assoc (fuelLLb b false σ (+ (size` (compile P) ℕ+ 1))) (fuelLLBS' semhl) f' with Lemma' semhl
  ... | pc'' ∣ semll' with stacklem1 {q = compile Q} (stacklem2 (bcomp b false (+ (size` (compile P) ℕ+ 1))) _ (stacklem1 {q = JMP (+ size` (compile Q)) :: []} semll'))
  ... | semll'* = pc'' z+ + size` (bcomp b false (+ (size` (compile P) ℕ+ 1))) ∣ (insertAtEnd* semll semll'*)

  --WhileFalse case.
  Lemma' {WHILE b DO c} {σ} {f' = f'} (WhileFalse x) rewrite x with Lemma2 b (compile c & (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) {f'} {$} {σ} x
  ... | semll rewrite size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} = (+ size` (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) ∣ semll



  -- WhileTrue case where guard, body and jump back to beginning are executed.
  Lemma' {WHILE b DO c} {σ} {f} {f'} (WhileTrue {s' = σ'}{f = suc f₀}{suc f*} {f**} x semhl semhl') rewrite x with Lemma3 b (compile c & (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) {fuelLLBS' semhl ℕ+ (1 ℕ+ fuelLLBS' semhl') ℕ+ f'} {$} {σ} x
  ... | semll rewrite size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} | +assoc (fuelLLb b false σ (+ (size` (compile c) ℕ+ 1))) (fuelLLBS' semhl ℕ+ (1 ℕ+ fuelLLBS' semhl')) f' | sym (+assoc (fuelLLBS' semhl) (suc (fuelLLBS' semhl')) f') with Lemma' semhl | Lemma' semhl'
  ... | pc' ∣ csemll | pc'' ∣ whilesemll with stacklem2 (bcomp b false (+ (size` (compile c) ℕ+ 1))) _ (stacklem1 {q = JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} csemll)
  ... | csemll' with addF* (suc (fuelLLBS' semhl') ℕ+ f') (subF*' {f' = 0} (suc f*) csemll')
  ... | csemll'' rewrite +assoc (fuelLLBS' semhl) (fuelLLBS' semhl') f' | Lemma'-helper semhl csemll = pc'' ∣ (insertAtEnd* semll (insertAtEnd* (insertAtEnd csemll'' helper) whilesemll))
    where
    helper : (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) ⊢⟦ config σ' $ (+ (size` (compile c) ℕ+ size` (bcomp b false (+ (size` (compile c) ℕ+ 1))))) , suc (fuelLLBS' semhl' ℕ+ f') ⟧⇒⟦ config σ' $ (+ 0) , fuelLLBS' semhl' ℕ+ f' ⟧
    helper rewrite &assoc (bcomp b false (+ (size` (compile c) ℕ+ 1))) (compile c) (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) | +comm (size` (compile c)) (size` (bcomp b false (+ (size` (compile c) ℕ+ 1)))) | sym (size`&+ {bcomp b false (+ (size` (compile c) ℕ+ 1))} {compile c}) with stacklem2b (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c) (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) {+ 0} refl
    ... | eq rewrite sym (size`&+ {bcomp b false (+ (size` (compile c) ℕ+ 1))} {compile c}) with ⊢JMP {((bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c) & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c) ℕ+ 1))) :: [])} {σ'} {$} {_} {_} {fuelLLBS' semhl' ℕ+ f'} eq
    ... | stp rewrite +comm (size` (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c)) 1 | n⊖n≡0 (size` (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c)) = stp

  -- WhileTrue case where guard is executed, body is partially/fully executed, but there is no fuel left to execute the next iteration of the loop.
  Lemma' {WHILE b DO c} {σ} {f} {f'} (WhileTrue {s' = σ'}{f = suc f*}{0}{f**} x semhl Empty) rewrite x with Lemma3 b (compile c & (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) {fuelLLBS' semhl ℕ+ f'} {$} {σ} x
  ... | semll rewrite size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} | +comm (fuelLLBS' semhl) 0 | +0 (fuelLLb b false σ (+ (size` (compile c) ℕ+ 1)) ℕ+ fuelLLBS' semhl) with Lemma' semhl
  ... | pc' ∣ csemll with stacklem2 (bcomp b false (+ (size` (compile c) ℕ+ 1))) _ (stacklem1 {q = JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} csemll)
  ... | csemll* rewrite +0 (fuelLLBS' semhl) = (pc' z+ + size` (bcomp b false (+ (size` (compile c) ℕ+ 1)))) ∣ insertAtEnd* semll {!csemll*!}



  -- WhileTrue case where guard is executed, but there is no fuel left to execute further.
  Lemma' {WHILE b DO c} {σ} {suc f} {f'} (WhileTrue {s' = σ'}{f = 0}{f*}{f**} x Empty Empty) rewrite x with Lemma3 b (compile c & (JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) {0} {$} {σ} x
  ... | semll rewrite size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} | +0 (fuelLLb b false σ (+ (size` (compile c) ℕ+ 1)) ℕ+ 0) = + size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ∣ semll

  
