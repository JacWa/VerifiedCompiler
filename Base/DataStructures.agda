module Base.DataStructures where

    -- Data... files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.Nat.Base
  open import Data.String.Base
  open import Data.Bool
  open import Misc.Base
  open import Level hiding (suc)

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

  infixr 10 _,_
  data Stack : Set where
    $   : Stack
    _,_ : ℕ → Stack → Stack

  height : Stack → ℕ
  height $       = 0
  height (h , t) = suc (height t)

  hd : Stack → ℕ
  hd $ = 0
  hd (n , _) = n

  tl : Stack → Stack
  tl $ = $
  tl (_ , t) = t

-----------------------
-- Config Definition --
-----------------------

  data Config : Set where
    config : (state : State)(stack : Stack)(pc : ℤ) → Config

  STATE : Config → State
  STATE (config state _ _) = state

  pc : Config → ℤ
  pc (config _ _ pc) = pc

  stack : Config → Stack
  stack (config _ stack _) = stack


---

  infixr 10 _×_
  data _×_ {a} (A B : Set a) : Set a where
    _,_ : (a : A)(b : B) → A × B
