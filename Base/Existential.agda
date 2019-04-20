module Base.Existential where

  open import Agda.Builtin.Sigma
  open import Level
  open import Data.Product using ()
  open import Data.Empty

  ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
  ∃-syntax = Σ _

  syntax ∃-syntax (λ x → B) = ∃[ x ] B
