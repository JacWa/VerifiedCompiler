module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Bool
  open import Relation.Binary
  open import Data.Nat.Base using (_≤_)
  import Level using (zero)

  is_≤_ : ℕ → ℕ → Bool
  is 0 ≤ x             = true
  is (suc y) ≤ 0       = false
  is (suc y) ≤ (suc x) = is y ≤ x

  infixr 20 _×_ _ω_
  data _ω_ {A B : Set} : Set → Set → Set where
    _×_ : (a : A)(b : B) → A ω B

  ∣_∣ : ℤ → ℕ
  ∣ pos x ∣ = x
  ∣ negsuc x ∣ = suc x

  _n-_ : ℕ → ℕ → ℤ
  x       n- 0       = pos x
  0       n- (suc y) = negsuc y
  (suc x) n- (suc y) = x n- y 

  infixl 20 _z+_
  _z+_ : ℤ → ℤ → ℤ
  (pos x)    z+ (pos y)    = pos (x + y)
  (pos x)    z+ (negsuc y) = x n- (suc y) 
  (negsuc x) z+ (pos y)    = y n- (suc x)  
  (negsuc x) z+ (negsuc y) = negsuc (suc (x + y))
  

  _z-_ : ℤ → ℤ → ℤ
  x z- (pos 0)       = x
  x z- (pos (suc y)) = x z+ (negsuc y)
  x z- (negsuc y)    = x z+ (pos (suc y))

  zuc : ℤ → ℤ
  zuc (negsuc 0)       = pos 0
  zuc (negsuc (suc x)) = negsuc x
  zuc (pos x)          = pos (suc x)

  neg : ℤ → ℤ
  neg (pos 0)       = pos 0
  neg (pos (suc x)) = negsuc x
  neg (negsuc x)    = pos (suc x)

  iz_≤_ : ℤ → ℤ → Bool
  iz (negsuc _) ≤ (pos _)    = true
  iz (pos _)    ≤ (negsuc _) = false 
  iz (pos x)    ≤ (pos y)    = is x ≤ y
  iz (negsuc x) ≤ (negsuc y) = is y ≤ x

  data _≤_`ℤ` : Rel ℤ Level.zero where
    -≤+ : ∀ {x y} →                  (negsuc x) ≤ (pos y)    `ℤ`
    +≤+ : ∀ {x y} → (p : x ≤ y) → (pos x)    ≤ (pos y)    `ℤ`
    -≤- : ∀ {x y} → (p : y ≤ x) → (negsuc x) ≤ (negsuc y) `ℤ`

  _<_`ℤ` : Rel ℤ Level.zero
  (negsuc 0)       < y `ℤ` = (pos 0)       ≤ y `ℤ`
  (negsuc (suc x)) < y `ℤ` = (negsuc x)    ≤ y `ℤ`
  (pos x)          < y `ℤ` = (pos (suc x)) ≤ y `ℤ`
