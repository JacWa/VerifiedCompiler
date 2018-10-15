module Proofs.Basic where

  open import Agda.Builtin.Equality

  -- proof: equality symmetry
  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl
  
  
