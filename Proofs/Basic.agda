module Proofs.Basic where

  open import Agda.Builtin.Equality
  open import Data.Bool.Base

  -- proof: equality symmetry
  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl
  
  itep : {p : Bool}{A : Set}{x y : A} → p ≡ false → x ≡ (if p then y else x)
  itep refl = refl
