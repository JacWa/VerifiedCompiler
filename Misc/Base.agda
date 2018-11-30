module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Relation.Binary
  open import Data.Nat.Base using (_≤_)
  open import Proofs.NatProofs
  import Level using (zero)

  is_≤_ : ℕ → ℕ → Bool
  is 0 ≤ x             = true
  is (suc y) ≤ 0       = false
  is (suc y) ≤ (suc x) = is y ≤ x

  infixr 20 _×_ _ω_
  data _ω_ {A B : Set} : Set → Set → Set where
    _×_ : (a : A)(b : B) → A ω B

  ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤trans {0} _ _ = _≤_.z≤n
  ≤trans {suc a} (_≤_.s≤s p) (_≤_.s≤s q) = _≤_.s≤s (≤trans p q)

  ≤+ : ∀ {x y z} → x ≤ y → x ≤ y + z
  ≤+ {0} _ = _≤_.z≤n
  ≤+ {suc n} (_≤_.s≤s p) = _≤_.s≤s (≤+ p)

  ≤= : ∀ {x} → x ≤ x
  ≤= {0} = _≤_.z≤n
  ≤= {suc x} = _≤_.s≤s ≤=

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
    
  ℤ≤trans : ∀ {x y z} → x ≤ y `ℤ` → y ≤ z `ℤ` → x ≤ z `ℤ`
  ℤ≤trans -≤+     (+≤+ _) = -≤+
  ℤ≤trans (-≤- _) -≤+     = -≤+
  ℤ≤trans (-≤- p) (-≤- q) = -≤- (≤trans q p)
  ℤ≤trans (+≤+ p) (+≤+ q) = +≤+ (≤trans p q)

  _<_`ℤ` : Rel ℤ Level.zero
  (negsuc 0)       < y `ℤ` = (pos 0)       ≤ y `ℤ`
  (negsuc (suc x)) < y `ℤ` = (negsuc x)    ≤ y `ℤ`
  (pos x)          < y `ℤ` = (pos (suc x)) ≤ y `ℤ`

  data _ℤ≡_ : Rel ℤ Level.zero where
    ℤzero : (pos 0) ℤ≡ (pos 0)
    ℤpos  : ∀ {x y} → (pos x) ℤ≡ (pos y) → (pos (suc x)) ℤ≡ (pos (suc y))
    ℤnero : (negsuc 0) ℤ≡ (negsuc 0)
    ℤneg  : ∀ {x y} → (negsuc x) ℤ≡ (negsuc y)


  _∨_ : Bool → Bool → Bool
  false ∨ b = b
  true ∨ b = true

  ∨split : ∀ {x y} → x ∨ y ≡ true → y ≡ false → x ≡ true
  ∨split {true} _ _ = refl
  ∨split {false} {true} _ ()
  ∨split {false} {false} ()

  ∨fs1 : ∀ {x y} → x ∨ y ≡ false → x ≡ false
  ∨fs1 {false} _ = refl
  ∨fs1 {true} ()

  ∨fs2 : ∀ {y x} → x ∨ y ≡ false → y ≡ false
  ∨fs2 {false} _ = refl
  ∨fs2 {true} {true} ()
  ∨fs2 {true} {false} ()
  
  ∨true : ∀ {x} → false ∨ x ≡ true → x ≡ true → false ∨ x ≡ true
  ∨true p q = q

  ∨false : ∀ {x y} → x ≡ false → y ≡ false → x ∨ y ≡ false
  ∨false refl refl = refl

  ∨false2 : ∀ {x} → x ≡ false → false ∨ x ≡ false
  ∨false2 p = p

  ∨switch : (b : Bool) → b ∨ false ≡ b
  ∨switch false = refl
  ∨switch true = refl

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  
