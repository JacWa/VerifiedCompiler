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
