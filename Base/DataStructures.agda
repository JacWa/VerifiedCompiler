module Base.DataStructures where

    -- Data... files are imported from agda-stdlib
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
-- State Definition --
----------------------

  data State : Set where
    ⟦⟧   : State
    _∷_ : Var → State → State

  get-var : String → State → ℕ
  get-var name ⟦⟧ = 0
  get-var name ((x ≔ val) ∷ vs) = if (primStringEquality name x) then val else (get-var name vs)

  set-var : String → ℕ → State → State
  set-var name newval ⟦⟧ = (name ≔ newval) ∷ ⟦⟧
  set-var name newval ((x ≔ val) ∷ vs) = if (primStringEquality name x) then ((x ≔ newval) ∷ ⟦⟧) else (((x ≔ val) ∷ (set-var name newval vs)))

----------------------
-- Stack Definition --
----------------------

  infixr 20 _,_
  data Stack : Set where
    $   : Stack
    _,_ : ℕ → Stack → Stack

  height : Stack → ℕ
  height $       = 0
  height (h , t) = suc (height t)

-----------------------
-- Config Definition --
-----------------------

  data Config : Set where
    config : (state : State)(stack : Stack)(pc : ℤ) → Config

  state : Config → State
  state (config state _ _) = state

  pC : Config → ℤ
  pC (config _ _ pc) = pc

  stack : Config → Stack
  stack (config _ stack _) = stack


---


