module Proofs.VerifiedCompilation where

  open import Semantics.HighLevel  
  open import Semantics.LowLevel

  open import Agda.Builtin.Sigma renaming (_,_ to _∣_)
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool


  open import Data.Nat using (suc; _≤?_) renaming (_+_ to _ℕ+_)
  open import Data.Nat.Properties using ()
  open import Data.Integer using (+_) renaming (_+_ to _z+_; suc to zuc)
  open import Data.Integer.Properties using (n⊖n≡0; +-comm; +-assoc)
  open import Data.Empty

  open import Lang.Expr
  open import Lang.Stack
  open import Compiler

  open import Base.DataStructures
  open import Base.Existential
  open import Base.Tuple renaming (_,_ to _~_)
  open import Base.Fuel
  open import Base.Inspect

  open import Proofs.ArithSemantics
  open import Proofs.BExpSemantics
  open import Proofs.Basic
  open import Proofs.BigStep.Base
  open import Proofs.NatProofs
  open import Proofs.Stack
  open import Proofs.Stack.Determinism
  
  open import Relation.Nullary

  open import Misc.Base using (neg; ≤trans; s≤→⊥)

  ------------------------------------------------------
  -- Proof of preservation of Semantics from HL to LL --
  ------------------------------------------------------


  Terminating : ∀ {I σ σ' f f'} (semhl : ⟦ I , σ , f ⟧↓⟦ σ' , f' ⟧) → compile I ⊢⟦ config σ $ (+ 0) , fuelLLBS↓ semhl ⟧⇒*⟦ config σ' $ (size (compile I)) , f' ⟧
  Terminating {.SKIP} Ski↓ = none
  Terminating {(x ≔ a)} Ass↓
    rewrite size`&+ {acomp a} {STORE x :: []} |
            +comm (size` (acomp a)) 1
    = Lemma1 {a}
    
  Terminating {this ⋯ that} (Seq↓ {f = f} {f'} {f''} sem-this sem-that) with Terminating sem-this | Terminating sem-that
  ... | sem-this-SML | sem-that-SML
    with stacklem1 {q = compile that} sem-this-SML | stacklem2 (compile this) _ sem-that-SML
  ... | sem-this-SML' | sem-that-SML'
    with subF*' f' sem-this-SML' | subF*' f'' sem-that-SML'
  ... | sem-this-SML'' | sem-that-SML~
    with addF* (fuelLLBS' (convert sem-that)) sem-this-SML''
  ... | sem-this-SML~
    with TransComp* sem-this-SML~ sem-that-SML~
  ... | sem-SML
    with addF* f'' sem-SML
  ... | sem-SML~
    rewrite size`&+ {compile this} {compile that} |
            +comm (size` (compile this)) (size` (compile that))
    = sem-SML~
    
  Terminating {(IF cond THEN this ELSE that)} (IfF↓ {f' = f'} cond≡f sem-that)
    with Lemma2 cond (compile this & JMP (+ size` (compile that)) :: []) {fuelLLBS' (convert sem-that)} {$} cond≡f 
  ... | sem-cond-SML
    rewrite size`&+ {compile this} {JMP (size (compile that)) :: []}
    with stacklem1 {q = compile that} sem-cond-SML
  ... | sem-cond-SML'
    with addF* f' sem-cond-SML'
  ... | sem-cond-SML~
    with Terminating sem-that
  ... | sem-that-SML
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1)) &
                    compile this &
                    JMP (+ size` (compile that)) :: [])
                   _
                   sem-that-SML
  ... | sem-that-SML~
    with TransComp* sem-cond-SML~ sem-that-SML~
  ... | sem-SML~
    rewrite size`&+ {bcomp cond false (+ (size` (compile this) ℕ+ 1)) &
                     compile this &
                     JMP (+ size` (compile that)) :: []}
                    {compile that} |
            +comm (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1)) &
                          compile this &
                          JMP (+ size` (compile that)) :: []))
                  (size` (compile that))
    = sem-SML~
    
  Terminating {(IF cond THEN this ELSE that)} (IfT↓ {f' = f'} cond≡t sem-this)
    with BSLem7 sem-this
  ... | p1 rewrite p1
    with Lemma3 cond (compile this & JMP (+ size` (compile that)) :: []) {fuelLLBS' (convert sem-this)} {$} cond≡t 
  ... | sem-cond-SML
    rewrite size`&+ {compile this} {JMP (size (compile that)) :: []}
    with stacklem1 {q = compile that} sem-cond-SML
  ... | sem-cond-SML'
    with addF* 1 sem-cond-SML'
  ... | sem-cond-SML''
    with addF* f' sem-cond-SML''
  ... | sem-cond-SML~
    with Terminating sem-this
  ... | sem-this-SML
    with stacklem1 {q = JMP (size (compile that)) :: []} sem-this-SML
  ... | sem-this-SML'
    with addF* 1 sem-this-SML'
  ... | sem-this-SML~
    rewrite sym (+assoc (fuelLLBS' (convert sem-this)) f' 1) |
            +comm f' 1 |
            +assoc (fuelLLBS' (convert sem-this)) 1 f'
    with TransComp sem-this-SML~ (⊢JMP (stacklem2c (compile this) (JMP (size (compile that))) []))
  ... | sem-this+JMP-SML
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this+JMP-SML
  ... | sem-this+JMP-SML'
    with stacklem1 {q = compile that} sem-this+JMP-SML'
  ... | sem-this+JMP-SML~
    with TransComp* sem-cond-SML~ sem-this+JMP-SML~
  ... | sem-SML~
    rewrite size`&+ {bcomp cond false (+ (size` (compile this) ℕ+ 1)) &
                     compile this &
                     JMP (+ size` (compile that)) :: []}
                    {compile that} | 
            size`&+ {bcomp cond false (+ (size` (compile this) ℕ+ 1))}
                    {compile this & JMP (+ size` (compile that)) :: []} |
            size`&+ {compile this} {JMP (+ size` (compile that)) :: []} |
            +comm (size` (compile this)) 1 |
            sym (+assoc (size` (bcomp cond false (+ suc (size` (compile this)))))
                        (suc (size` (compile this)))
                        (size` (compile that))) |
            +comm (size` (bcomp cond false (+ suc (size` (compile this)))))
                  (suc (size` (compile this) ℕ+ size` (compile that)))
    = sem-SML~

  Terminating {WHILE cond DO this} (WhF↓ {f = f} cond≡f)
    with Lemma2 cond (compile this & JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []) {f} {$} cond≡f
  ... | sem-cond-SML~
    rewrite size`&+ {compile this} {JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []}
    = sem-cond-SML~
    
  Terminating {WHILE cond DO this} (WhT↓ {f' = f'} {f''} cond≡t sem-this sem-rest)
    with BSLem7 sem-this
  ... | p1 rewrite p1
    with Lemma3 cond (compile this & JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []) {(fuelLLBS' (convert sem-this) ℕ+ suc (fuelLLBS' (convert sem-rest)))} {$} cond≡t 
  ... | sem-cond-SML
    with Terminating sem-this | Terminating sem-rest
  ... | sem-this-SML | sem-rest-SML
    with subF*' f' sem-this-SML
  ... | sem-this-SML'
    with addF* (suc (fuelLLBS' (convert sem-rest))) sem-this-SML'
  ... | sem-this-SML''
    with stacklem1 {q = JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+
                                     size` (compile this) ℕ+ 1)))
                        :: []}
                        sem-this-SML''
  ... | sem-this-SML'''
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this-SML'''
  ... | sem-this-SML''''
    rewrite +comm (size` (compile this)) (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))))
    with (stacklem2c (compile this)
                     (JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+
                                   size` (compile this) ℕ+ 1))))
                     ([]))
  ... | p2
    with TransComp sem-this-SML'''' (⊢JMP (stacklem2b' (bcomp cond false (+ (size` (compile this) ℕ+ 1))) p2))
  ... | sem-this+JMP-SML
    rewrite size`&+ {compile this} {JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []} | a+b+c≡c+a+b (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1)))) (size` (compile this)) 1 | n⊖n≡0 (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this))
    with TransComp* sem-cond-SML sem-this+JMP-SML
  ... | sem-one-iter-SML
    with addF* f'' sem-one-iter-SML
  ... | sem-one-iter-SML'
    = TransComp* sem-one-iter-SML' sem-rest-SML



  Lemma : ∀ I {σ f f' σ'} → (semhl : ⟦ I , σ , f ⟧⇛⟦ σ' , f' ⟧) → ∃[ pc' ] (compile I ⊢⟦ config σ $ (+ 0) , fuelLLBS semhl ⟧⇒*⟦ config σ' $ pc' , f' ⟧)
    
  Lemma _ Empty = + 0 ∣ none
    
  Lemma SKIP Skip = + 0 ∣ none
    
  Lemma (x ≔ a) {σ} {suc f} Assign = + suc (size` (acomp a)) ∣ Lemma1 {a}
    
  Lemma (this ⋯ that) (Seq {f' = f'} {f''} sem-this sem-that)
  -- Split cases where "this" fully executes or runs out of fuel.
     with inspect (BSLem3 sem-this)
      
  -- "this" fully executes.
  ... | true with≡ proof
  -- Generate the semantics for executing "that"
     with Lemma that sem-that
  ... | pc-that ∣ sem-that-SML
  -- Modify the program in the semantics to be the entire program.
     with stacklem2 (compile this) _ sem-that-SML
  ... | sem-that-SML~
  -- Generate semantics for executing "this".
     with inspect (convert₃ sem-this proof)
  ... | term-sem-this with≡ 1p
    with Terminating term-sem-this
  ... | sem-this-SML
    rewrite sym 1p | revert₃ sem-this proof
  -- Amend the amount of fuel/=.
    with subF*' f' sem-this-SML
  ... | sem-this-SML'
    with addF* (fuelLLBS' sem-that) sem-this-SML'
  ... | sem-this-SML''
    with addF* f'' sem-this-SML''
  ... | sem-this-SML'''
  -- Add the complete program to te semantics.
    with stacklem1 {q = compile that} sem-this-SML'''
  ... | sem-this-SML~
    = pc-that z+ (size (compile this)) ∣ TransComp* sem-this-SML~ sem-that-SML~  
                                                                    
  -- Fuel runs out while executing "this".
  Lemma (this ⋯ that) (Seq sem-this sem-that) | false with≡ proof
  -- Rewrite by proof that [f' ≡ 0].
    with BSLem6 sem-this proof
  Lemma (this ⋯ that) (Seq sem-this Empty) | false with≡ proof | refl 
  -- Generate the semantics for executing "this".
    with Lemma this sem-this
  ... | pc-this ∣ sem-this-SML
  -- Modify the program in the semantics to be the entire program.
    with stacklem1 {q = compile that} sem-this-SML
  ... | sem-this-SML~
    rewrite +comm (fuelLLBS' sem-this ℕ+ 0) 0
    = pc-this ∣ sem-this-SML~

  Lemma (IF cond THEN this ELSE that) {σ} (IfFalse {f' = f'} cond≡f sem-that)
  -- ⬐ Generate semantics for executing the condition.
    with Lemma2 cond (compile this & JMP (size (compile that)) :: []) {fuelLLBS' sem-that ℕ+ f'} {$} cond≡f
  ... | cond-sem
  -- ⬐ Rewrite fuel so that it matches the expected initial fuel.
    rewrite size`&+ {compile this} {JMP (size (compile that)) :: []} |
            +assoc (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1))) (fuelLLBS' sem-that) f'
  -- ⬐ Append "compile that" to the program in the semantics for the condition.
    with stacklem1 {q = compile that} cond-sem
  ... | cond-sem~
  -- ⬐ Generate the semantics for executing the else-block, "that".
    with Lemma that sem-that
  ... | pc-that ∣ sem-that-SML
  -- ⬐ Prepend the program in the semantics with the condition, "compile this" and the jump instruction.
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1)) & compile this & JMP (+ size` (compile that)) :: []) _ sem-that-SML
  ... | sem-that-SML~
    = _ ∣ TransComp* cond-sem~ sem-that-SML~
           
  Lemma (IF cond THEN this ELSE that) {σ} (IfTrue {f' = f'} cond≡t sem-this)
  
  -- Split case on whether there is enough fuel to fully execute "this".
    with inspect (BSLem3 sem-this)
    
  -- Case where there is enough fuel to execute "this".
  ... | true with≡ proof rewrite proof 
  -- ⬐ Generate semantics for executing the condition.
    with Lemma3 cond (compile this & JMP (size (compile that)) :: []) {fuelLLBS' sem-this ℕ+ 1 ℕ+ f'} {$} cond≡t
  ... | cond-sem
    -- ⬐ Rewrite fuel so that it matches the expected initial fuel.
    rewrite size`&+ {compile this} {JMP (size (compile that)) :: []} |
            +assoc (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1))) (fuelLLBS' sem-this ℕ+ 1) f' |
            +assoc (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1))) (fuelLLBS' sem-this) 1 |
            +comm (fuelLLBS' sem-this) 1
  -- ⬐ Append "compile that" to the program in the semantics for the condition.
    with stacklem1 {q = compile that} cond-sem
  ... | cond-sem' 
  -- ⬐ Generate the semantics for executing the else-block, "this".
    with inspect (convert₃ sem-this proof)
  ... | term-sem-this with≡ p1
    with Terminating term-sem-this
  ... | sem-this-SML rewrite sym p1 | revert₃ sem-this proof
  -- ⬐ Append jump command to the program.
    with stacklem1 {q = JMP (size (compile that)) :: []} sem-this-SML
  ... | sem-this-SML'
  -- ⬐ Add fuel to execute jump command.
    with addF*' 1 sem-this-SML'
  ... | sem-this-SML''
  -- ⬐ Execute jump command.
    with TransComp sem-this-SML'' (⊢JMP (stacklem2c (compile this) (JMP (size (compile that))) []))
  ... | sem-this&JMP-SML
  -- ⬐ Complete the program in the above semantics
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this&JMP-SML
  ... | sem-this&JMP-SML'
    with stacklem1 {q = compile that} sem-this&JMP-SML'
  ... | sem-this&JMP-SML''
    = _ ∣ TransComp* cond-sem' sem-this&JMP-SML''
      
  -- Case where there is not enough fuel to fully execute "this".
  Lemma (IF cond THEN this ELSE that) {σ} (IfTrue cond≡t sem-this) | false with≡ proof rewrite proof
  -- ⬐ Generate semantics for executing the condition.
    with Lemma3 cond (compile this & JMP (size (compile that)) :: []) {fuelLLBS' sem-this ℕ+ 0} {$} cond≡t
  ... | cond-sem
  -- ⬐ Rewrite fuel so that it matches the expected initial fuel.
    rewrite size`&+ {compile this} {JMP (size (compile that)) :: []} |
            +assoc (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1)))
                   (fuelLLBS' sem-this)
                   0
  -- ⬐ Append "compile that" to the program in the semantics for the condition.
    with stacklem1 {q = compile that} cond-sem
  ... | cond-sem' 
  -- Rewrite by proof that [f' ≡ 0].
    with BSLem6 sem-this proof
  ... | refl
  -- ⬐ Generate the semantics for executing the else-block, "this".
    with Lemma this sem-this
  ... | pc' ∣ sem-this-SML
  -- ⬐ Complete the program in the above semantics.
    with stacklem1 {q = JMP (size (compile that)) :: []} sem-this-SML
  ... | sem-this-SML'
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this-SML'
  ... | sem-this-SML''
    with stacklem1 {q = compile that} sem-this-SML''
  ... | sem-this-SML~
    = _ ∣ (TransComp* cond-sem' sem-this-SML~)
       
  Lemma (WHILE cond DO this) (WhileFalse {f = f} cond≡f) rewrite cond≡f
    with Lemma2 cond (compile this & JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []) {f} {$} cond≡f
  ... | cond-sem
    rewrite size`&+ {compile this}
                    {JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []}
    = _ ∣ cond-sem
    
  Lemma (WHILE cond DO this) {σ} (WhileTrue {f' = f'} {f''} cond≡t sem-this sem-rest)
  -- ⬐ Generate semantics for executing the condition.
    with Lemma3 cond (compile this & JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []) {fuelLLBS' sem-this} {$} cond≡t
  ... | cond-sem 
    rewrite size`&+ {compile this}
                    {JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []}

  -- Split case on whether the first iteration of "this" has enough fuel to fully execute.
    with inspect (BSLem3 sem-this)

  -- Case where there is enough fuel to fully execute "this".
  ... | true with≡ p1 rewrite p1
  -- ⬐ Generate the semantics for executing the rest of the while loop.
    with Lemma (WHILE cond DO this) sem-rest
  ... | pc' ∣ sem-rest-SML
  -- Generate semantics for executing "this".
    with inspect (convert₃ sem-this p1)
  ... | term-sem-this with≡ p2
    with Terminating term-sem-this
  ... | sem-this-SML rewrite sym p2 | revert₃ sem-this p1
  -- Append the jump command to the program in the semantics for "this".
    with stacklem1 {q = JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []} sem-this-SML
  ... | sem-this-SML'
  -- Add 1 fuel to execute jump command, and remove f' fuel.
    with subF*' f' sem-this-SML'
  ... | sem-this-SML''
    with addF*' 1 sem-this-SML''
  ... | sem-this-SML~
  -- Execute jump.
    with TransComp sem-this-SML~
                   (⊢JMP (stacklem2c (compile this)
                                     (JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))))
                                     []))
  ... | sem-this&JMP-SML
  -- ⬐ Complete program in the above semantics
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this&JMP-SML
  ... | sem-this&JMP-SML'
  -- ⬐ Rewrites to show that after executing the first loop, the program counter = 0.
    rewrite +-comm (+ suc (size` (compile this))) (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) |
            +-assoc (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1)))
                    (+ suc (size` (compile this)))
                    (+ size` (bcomp cond false (+ (size` (compile this) ℕ+ 1)))) |
            a+b+c≡c+a+b (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1)))) (size` (compile this)) 1 |
            +comm (size` (compile this)) (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1)))) |
            n⊖n≡0 (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this)) 
  -- Add fuel for the rest of the while loop.
    with addF* (fuelLLBS' sem-rest ℕ+ f'') sem-this&JMP-SML'
  ... | sem-this&JMP-SML~
  -- ⬐ Join semantics for "this" and the jump with the semantics of the rest of the loop.
    with TransComp* sem-this&JMP-SML~ sem-rest-SML
  ... | sem-this&rest-SML
  -- ⬐ Rewrites to match fuel.
    with addF* (fuelLLBS' sem-rest ℕ+ f'') cond-sem
  ... | cond-sem'
    with addF*' 1 cond-sem'
  ... | cond-sem~
    rewrite +assoc (fuelLLBS' sem-this) (fuelLLBS' sem-rest) f'' 
    with +match (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1)))
                (fuelLLBS' sem-this)
                (fuelLLBS' sem-rest)
                f''
      where
      +match : ∀ a b c d → a ℕ+ (b ℕ+ suc c) ℕ+ d ≡ suc (a ℕ+ b ℕ+ (c ℕ+ d))
      +match a b c d
        rewrite +assoc a b (suc c)   |
                +assoc (a ℕ+ b) 1 c |
                a+b+c≡c+a+b a b 1    |
                +comm a 1            |
                +assoc (a ℕ+ b) c d
        = refl
  ... | p3 rewrite p3 = _ ∣ TransComp* cond-sem~ sem-this&rest-SML
       
  -- Case where there is not enough fuel to fully execute "this".
  Lemma (WHILE cond DO this) (WhileTrue {f' = f'} {f''} cond≡t sem-this sem-rest) | cond-sem | false with≡ p1 rewrite p1
    -- ⬐ Rewrite by proof that f' ≡ 0.
    with BSLem6 sem-this p1
  Lemma (WHILE cond DO this) {σ} (WhileTrue cond≡t sem-this Empty) | cond-sem | _ | refl
    -- ⬐ Generate semantics for the execution of "this".
    with Lemma this sem-this
  ... | pc' ∣ sem-this-SML
    -- ⬐ Complete the program in the above semantics.
    with stacklem1 {q = JMP (neg (+ (size` (bcomp cond false (+ (size` (compile this) ℕ+ 1))) ℕ+ size` (compile this) ℕ+ 1))) :: []} sem-this-SML
  ... | sem-this-SML'
    with stacklem2 (bcomp cond false (+ (size` (compile this) ℕ+ 1))) _ sem-this-SML'
  ... | sem-this-SML~
    -- Fix fuel in cond-sem to match sem-this-SML~.
    with addF* 0 cond-sem
  ... | cond-sem~
    -- ⬐ Join the semantics of the condition and "this".
    with TransComp* cond-sem~ sem-this-SML~
  ... | full-sem-SML
    -- ⬐ Fix the fuel to match goal.
    rewrite +assoc (fuelLLb cond false σ (+ (size` (compile this) ℕ+ 1)))
                   (fuelLLBS' sem-this)
                   0
    with addF* 0 full-sem-SML
  ... | full-sem-SML~
    = _ ∣ full-sem-SML~
                                                                      

