module Base.Tuple where

  open import Level

  ------------------------------
  -- Module for simple tuples --
  ------------------------------
  infixr 6 _×_ _,_
  data _×_ {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
    _,_ : (x : A)(y : B) → A × B

  l : ∀ {a b}{A : Set a}{B : Set b} → A × B → A
  l (a , _) = a

  r : ∀ {a b}{A : Set a}{B : Set b} → A × B → B
  r (_ , b) = b
