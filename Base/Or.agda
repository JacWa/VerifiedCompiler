module Base.Or where

  open import Level

  data _∨_ {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
    left  : (a : A) → A ∨ B
    right : (b : B) → A ∨ B
