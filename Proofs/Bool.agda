module Proofs.Bool where

  open import Data.Bool
  open import Data.Empty
  open import Relation.Nullary
  open import Agda.Builtin.Equality


  ∧-false : ∀ {b' b} → ¬ b' ≡ false → b' ∧ b ≡ false → b ≡ false
  ∧-false {true} _ x = x
  ∧-false {false} x _ = ⊥-elim (x refl)
  
  ∧-true : ∀ {b' b} → ¬ b' ≡ true → b' ∧ b ≡ true → ⊥
  ∧-true {true} x _ = ⊥-elim (x refl)
  ∧-true {false} _ ()

  ¬-false : ∀ {b} → ¬ b ≡ false → b ≡ true
  ¬-false {false} x = ⊥-elim (x refl)
  ¬-false {true} x = refl

  ¬-true : ∀ {b} → ¬ b ≡ true → b ≡ false
  ¬-true {true} x = ⊥-elim (x refl)
  ¬-true {false} x = refl




  bool⊥' : true ≡ false → ⊥
  bool⊥' ()

  bool⊥ : false ≡ true → ⊥
  bool⊥ ()

  notfalse : ∀ {b} → not b ≡ false → b ≡ true
  notfalse {false} ()
  notfalse {true} a = refl

  nottrue : ∀ {b} → not b ≡ true → b ≡ false
  nottrue {false} y = refl
  nottrue {true} ()
