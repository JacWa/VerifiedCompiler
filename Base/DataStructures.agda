module Base.DataStructures where

  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  
  open import Data.Nat.Base
  open import Data.String.Base
  open import Data.Bool

  open import Misc.Base

-------------------------
-- Variable Definition --
-------------------------

  data Var : Set where
    _≔_ : (name : String) → (val : ℕ) → Var

----------------------
-- Store Definition --
----------------------

  -- Store for variable assignment.
  data Store : Set where
    ⟦⟧   : Store
    _∷_ : Var → Store → Store

  get-var : String → Store → ℕ
  get-var name ⟦⟧ = 0
  get-var name ((x ≔ val) ∷ vs) = if (primStringEquality name x) then val else (get-var name vs)


----------------------
-- Stack Definition --
----------------------

  -- Stack for low level execution.
  infixr 20 _,_
  data Stack : Set where
    $   : Stack
    _,_ : ℕ → Stack → Stack

  hd : Stack → ℕ
  hd $ = 0
  hd (n , _) = n

  tl : Stack → Stack
  tl $ = $
  tl (_ , t) = t

-----------------------
-- Config Definition --
-----------------------

  
  -- Config (state) for low level execution.
  data Config : Set where
    config : (store : Store)(stack : Stack)(pc : ℤ) → Config

  pc : Config → ℤ
  pc (config _ _ pc) = pc

  stack : Config → Stack
  stack (config _ stack _) = stack



