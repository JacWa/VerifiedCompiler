module Proofs.Basic where

  open import Agda.Builtin.Equality
  open import Data.Bool.Base

  -----------------------------
  -- Basic equality symmetry --
  -----------------------------
  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl
