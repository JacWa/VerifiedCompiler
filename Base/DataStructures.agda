module Base.DataStructures where

    -- Data... files are imported from agda-stdlib
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.Nat.Base
  open import Data.String.Base
  open import Data.Bool

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
  data Stack : ℕ → Set where
    $   : Stack 0
    _,_ : ∀ {n} → ℕ → Stack n → Stack (suc n)

-----------------------
-- Config Definition --
-----------------------

  data Config : ℕ → Set where
    config : ∀ {h}(state : State)(stack : Stack h)(pc : ℕ) → Config h

  getState : ∀ {h} → Config h → State
  getState (config state _ _) = state

  gssc : {h : ℕ}{pc : ℕ}{stack : Stack h}{state : State} → state ≡ getState (config state stack pc)
  gssc = refl

---

  data Diff : ℕ → Set where
    +one    : Diff 0
    none'nj : Diff 2
    none'cj : Diff 0
    -one'st : Diff 1
    -one'ad : Diff 2

  diff : (x : ℕ){mh : ℕ} → Diff mh → {pr1 : mh ≤ x} → ℕ
  diff h       (+one)    = suc h
  diff h       (none'nj) = h
  diff h       (none'cj) = h
  diff (suc h) (-one'st) = h
  diff (suc h) (-one'ad) = h
  diff 0       (-one'st) {}
  diff 0       (-one'ad) {}
  
