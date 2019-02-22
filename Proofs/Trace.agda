module Proofs.Trace where

  open import Relation.Binary
  open import Relation.Binary.Core
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.TrustMe
  open import Relation.Nullary
  open import Function
  
  open import Data.Empty
  open import Data.Bool renaming (_≟_ to _≟'_)
  open import Data.String renaming (_≟_ to _≟''_)
  open import Data.Nat.Base renaming (_≟_ to _≟'''_)
  open import Data.List
  
  open import Lang.Expr
  open import Lang.Stack
  open import Compiler
  open import Trace





  transEQ : ∀ {f f`}(P : IExp) → traceᴴᴸ f P ≡ traceᴸᴸ f` (compile P)
  transEQ = ?









{-
{-  _≈_ : Decidable {A = Bhvr} _≡_
  RD x y ≈ RD a b with x ≟' a | y ≟'' b
  ... | yes p | yes q rewrite p | q = yes refl
  ... | _ | no q = no (λ t → q {!!})
  RD _ _ ≈ WRT _ _ = no (λ ())
  WRT _ _ ≈ RD _ _ = no (λ ())
-}

  _`≟_ : Bhvr → Bhvr → Bool
  RD _ _ `≟ WRT _ _ = false
  WRT _ _ `≟ RD _ _ = false
  
  eq-helper1 : {x : Bhvr}(xs ys : List Bhvr) → xs ≡ ys → x ∷ xs ≡ x ∷ ys
  eq-helper1 [] [] _ = refl
  eq-helper1 (x ∷ xs) (y ∷ ys) p rewrite p = refl
  eq-helper1 [] (y ∷ ys) ()
  eq-helper1 (x ∷ xs) [] ()

  eq-helper2 : (x y : Bhvr){xs : List Bhvr} → x ∷ xs ≡ y ∷ xs → x ≡ y
  eq-helper2 x y refl = refl
  {-
  eq-help : {x y : Bhvr}{xs ys : List Bhvr} → Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
  eq-help (yes p) (yes q) rewrite p | q = yes refl
  eq-help (no p)  _ = no {!!}

  _≟_ : Decidable {A = List Bhvr} _≡_
  [] ≟ [] = yes refl
  (x ∷ xs) ≟ (y ∷ ys) = eq-help (x  y) (xs ≟ ys)
  (_ ∷ _) ≟ [] = no λ ()
  [] ≟ (_ ∷ _) = no λ ()
  

-}-}
