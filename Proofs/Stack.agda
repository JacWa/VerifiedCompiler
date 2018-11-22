module Proofs.Stack where

  open import Lang.Stack
  open import Base.DataStructures
  open import Data.Bool
  open import Misc.Base
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality

  p'exec? : ∀ {h1 h2} → Prog → Config h1 → Config h2 → Bool
  p'exec? p (config state stack pc) c2 with (p ! pc) | c2
  ... | (x :: xs) | .(iexe refl x (config state stack pc)) = if (iz (pos 0) ≤ pc) then (if (iz (zuc pc) ≤ (size p)) then true else false) else false
  ... | _ | _ = false
