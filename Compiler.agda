module Compiler where

  -- Data... files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Misc.Base

-------------------------
-- Variable definition --
-------------------------

  data Var : Set where
    _≔_ : (name : String) → (val : ℕ) → Var


  data State : Set where
    ⟦⟧   : State
    _∷_ : Var → State → State

  get-var : String → State → ℕ
  get-var name ⟦⟧ = 0
  get-var name ((x ≔ val) ∷ vs) = if (primStringEquality name x) then val else (get-var name vs)

  set-var : String → ℕ → State → State
  set-var name newval ⟦⟧ = (name ≔ newval) ∷ ⟦⟧
  set-var name newval ((x ≔ val) ∷ vs) = if (primStringEquality name x) then ((x ≔ newval) ∷ ⟦⟧) else (((x ≔ val) ∷ (set-var name newval vs)))


----------------------------
-- Expression definitions --
----------------------------

  -- Arithmetic Expressions
  data AExp : Set where  
    NAT   : ℕ → AExp
    VAR   : String → AExp
    _+_   : AExp → AExp → AExp

  -- Boolean Expressions
  data BExp : Set where
    BOOL    : Bool → BExp
    NOT     : BExp → BExp
    _AND_   : BExp → BExp → BExp
    _LT_    : AExp → AExp → BExp

  -- Instructions
  infixl 20 _⋯_
  data IExp : Set where
    SKIP          : IExp
    _≔_          : String → AExp → IExp
    _⋯_          : IExp → IExp → IExp
    IF_THEN_ELSE_ : BExp → IExp → IExp → IExp
    WHILE_DO_     : BExp → IExp → IExp


  -- Execute arithmetic expressions
  aexe : AExp → State → ℕ
  aexe (NAT val)  _     = val
  aexe (VAR name) state = get-var name state 
  aexe (x + y)    state = (aexe x state) ℕ+ (aexe y state)

  -- Execute boolean expressions
  bexe : BExp → State → Bool
  bexe (BOOL b)  _     = b
  bexe (NOT x)   state = not (bexe x state)
  bexe (x AND y) state = (bexe x state) ∧ (bexe y state)
  bexe (m LT n)  state = (aexe m state) < (aexe n state)

  --BigStep
  data [_,_]↦_ : IExp → State → State → Set where
    Skip       : ∀ {s} → [ SKIP , s ]↦ s
    Assign     : ∀ {x n s} → [ (x ≔ n) , s ]↦ (set-var x (aexe n s) s)
    Seq        : ∀ {s1 s2 s3 this that} → [ this , s1 ]↦ s2 → [ that , s2 ]↦ s3 → [ (this ⋯ that) , s1 ]↦ s3
    IfFalse    : ∀ {s t bool this that}{p : (bexe bool s) ≡ false} → [ that , s ]↦ t → [ (IF bool THEN this ELSE that) , s ]↦ t
    IfTrue     : ∀ {s t bool this that}{p : (bexe bool s) ≡ true}  → [ this , s ]↦ t → [ (IF bool THEN this ELSE that) , s ]↦ t
    WhileFalse : ∀ {s bool this}{p : (bexe bool s) ≡ false} → [ (WHILE bool DO this) , s ]↦ s
    WhileTrue  : ∀ {s1 s2 s3 bool this}{p : (bexe bool s1) ≡ true} → (first : [ this , s1 ]↦ s2) → (then : [ (WHILE bool DO this) , s2 ]↦ s3) → [ (WHILE bool DO this) , s1 ]↦ s3

  -- Execute instructions

  
  
  

{---------------------
-- Stack language --
--------------------

  -- definition of Stack, indexed by a natural number representing stack height
  infixr 20 _,_
  data Stack : ℕ → Set where
    $   : Stack 0
    _,_ : ∀ {n} → ℕ → Stack n → Stack (suc n)

  -- definition of instructions that can be used to manipulate stack, indexed by 2 natural numbers representing stack height before and after instruction execution respectively.
  data Inst : ℕ → ℕ → Set where
    loadi : ∀ {h} → ℕ      → Inst h (suc h)
    load  : ∀ {h} → String → Inst h (suc h)
    add   : ∀ {h}           → Inst (suc (suc h)) (suc h)

  -- definition of list of Inst, i.e. a stack program. indexed by two numbers representing stack height before and after program execution respectively.
  infixr 20 _::_
  data Path : ℕ → ℕ → Set where
    ─     : ∀ {x} → Path x x
    _::_  : ∀ {x y z} → Inst x y → Path y z → Path x z

  -- function: join two SML programs
  infixl 20 _>>_
  _>>_ : ∀ {x y z} → Path x y → Path y z → Path x z
  ─         >> l = l                                        
  (x :: xs) >> l = (x :: (xs >> l))

  -- function: execute Stack Machine Language (SML) program
  exs : ∀ {x y} → Path x y → List Var → Stack x → Stack y
  exs ─ _ stack = stack
  exs ((loadi val) :: xs) env stack            = exs xs env (val                  , stack)
  exs ((load name) :: xs) env stack            = exs xs env ((get-var name env) , stack)
  exs (add         :: xs) env (y1 , y2 , rest) = exs xs env ((y2 ℕ+ y1)           , rest)
-}
--------------
-- Compiler --
--------------
{-
  -- function: compile ETL to SML
  compile : ∀ {n} → Exp → Path n (suc n)
  compile (nat val)  = (loadi val) :: ─
  compile (var name) = (load name) :: ─
  compile (e1 + e2)  = (compile e1) >> (compile e2) >> (add :: ─)


------------------
-- Verification --
------------------

  -- proof: distributive(?) property of exs and _>>_
  >>-ex : ∀ {x y z}(env : List Var)(s : Stack x)(a : Path x y)(b : Path y z) → exs (a >> b) env s ≡ exs b env (exs a env s)
  >>-ex _ _ ─ b = refl
  >>-ex env s (a :: as) b with a | s
  ... | loadi val | ss             = >>-ex env (val                  , ss) as b
  ... | load name | ss             = >>-ex env ((get-var name env) , ss) as b
  ... | add       | (s1 , s2 , ss) = >>-ex env ((s2 ℕ+ s1)           , ss) as b
  
  -- verification of compiler
  verify : ∀ {n} (exp : Exp)(xs : Stack n)(env : List Var) → (exe exp env) , xs ≡ exs (compile exp) env xs
  verify (nat val)  _ _ = refl
  verify (var name) _ _ = refl
  verify (exp₁ + exp₂) xs env rewrite >>-ex env xs ((compile exp₁) >> (compile exp₂)) (add :: ─) | >>-ex env xs (compile exp₁) (compile exp₂) | sym (verify exp₁ xs env) | sym (verify exp₂ (exe exp₁ env , xs) env) = refl
-}
