module Lang.Expr where

  -- Data.* files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
  open import Base.DataStructures
  
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
  
  
