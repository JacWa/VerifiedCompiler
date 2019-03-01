module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality


  open import Relation.Binary
  open import Data.Nat.Base using (_≤_)
  open import Proofs.NatProofs
  open import Proofs.Basic
  import Level using (zero)

  is_≤_ : ℕ → ℕ → Bool
  is 0 ≤ x             = true
  is (suc y) ≤ 0       = false
  is (suc y) ≤ (suc x) = is y ≤ x

  ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤trans {0} _ _ = _≤_.z≤n
  ≤trans {suc a} (_≤_.s≤s p) (_≤_.s≤s q) = _≤_.s≤s (≤trans p q)

  ≤+ : ∀ {x y z} → x ≤ y → x ≤ y + z
  ≤+ {0} _ = _≤_.z≤n
  ≤+ {suc n} (_≤_.s≤s p) = _≤_.s≤s (≤+ p)

  ≤s : ∀ {x} y → x ≤ y → x ≤ (suc y)
  ≤s {0} _ _ = _≤_.z≤n
  ≤s {suc n} (suc y) (_≤_.s≤s p) = _≤_.s≤s (≤s y p)

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

  0+z : ∀ z → pos 0 z+ z ≡ z
  0+z (pos n) = refl
  0+z (negsuc n) = refl

  z+0 : ∀ z → z z+ pos 0 ≡ z
  z+0 (pos n) rewrite +0 n = refl
  z+0 (negsuc n) = refl

  _z-_ : ℤ → ℤ → ℤ
  x z- (pos 0)       = x
  x z- (pos (suc y)) = x z+ (negsuc y)
  x z- (negsuc y)    = x z+ (pos (suc y))

  _∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
  (f ∘ g) x = g (f x) 

  zuc : ℤ → ℤ
  zuc (negsuc 0)       = pos 0
  zuc (negsuc (suc x)) = negsuc x
  zuc (pos x)          = pos (suc x)

  z++ : ∀ x y → pos (suc (x + y)) ≡ zuc (pos x z+ pos y)
  z++ x y = refl

  z+comm : ∀ x y → x z+ y ≡ y z+ x
  z+comm (pos x)    (pos y)    rewrite +comm x y = refl
  z+comm (negsuc x) (negsuc y) rewrite +comm x y = refl
  z+comm (pos x)    (negsuc y) = refl
  z+comm (negsuc x) (pos y)    = refl

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
  (pos x)          < y `ℤ` = (zuc (pos x)) ≤ y `ℤ`

  ℤ<zuc : ∀ x y → x < y `ℤ` → x < zuc y `ℤ`
  ℤ<zuc (negsuc (suc a)) (pos b) p  = -≤+
  ℤ<zuc (negsuc 0) (pos b) p  = +≤+ _≤_.z≤n
  ℤ<zuc (pos a) (pos (suc b)) p with p
  ... | +≤+ q = +≤+ (≤s (suc b) q)
  ℤ<zuc (negsuc (suc (suc n))) (negsuc (suc x)) p with p
  ... | -≤- (_≤_.s≤s q) = -≤- (≤s n q)
  ℤ<zuc (negsuc (suc n)) (negsuc 0) p = -≤+
  
  ℤ<zuc (negsuc 1) (negsuc (suc n)) (-≤- ())
  ℤ<zuc (pos n) (pos 0) (+≤+ ())
  ℤ<zuc (pos n) (negsuc x) ()
  ℤ<zuc (negsuc 0) (negsuc n) ()

  +-zuc : ∀ x z → pos (suc x) z+ negsuc z ≡ zuc (pos x z+ negsuc z)
  +-zuc 0 0 = refl
  +-zuc 0 (suc n) = refl
  +-zuc (suc x) 0 = refl
  +-zuc (suc x) (suc z) = +-zuc x z

  ℤ<+ : ∀ {x y z} → (pos 0) ≤ x `ℤ` → y < z `ℤ` → y < (x z+ z) `ℤ`
  ℤ<+ {pos 0} {z = z} p q rewrite 0+z z = q
  ℤ<+ {pos (suc n)} {y} {pos z} p q = ℤ<zuc y (pos (n + z)) (ℤ<+ (+≤+ _≤_.z≤n) q)
  ℤ<+ {pos (suc x)} {negsuc (suc y)} {negsuc z} p q rewrite +-zuc x z = ℤ<zuc (negsuc (suc y)) (pos x z+ negsuc z) (ℤ<+ {pos x} {negsuc (suc y)} {negsuc z} (+≤+ _≤_.z≤n) q)
  ℤ<+ {negsuc n} ()
  ℤ<+ {_} {negsuc 0} {negsuc z} _ ()
  ℤ<+ {_} {pos y} {negsuc z} _ ()

  ℤ<+s : ∀ {x y z} → (pos 0) ≤ x `ℤ` → y < z `ℤ` → y < (z z+ x) `ℤ`
  ℤ<+s {x} {y} {z} p q rewrite z+comm z x = ℤ<+ p q
  
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

  
  ! : Bool → Bool
  ! false = true
  ! true = false

  _∧_ : Bool → Bool → Bool
  false ∧ _ = false
  true ∧ b = b

  sucn : ℤ → ℕ → ℤ
  sucn z                0       = z
  sucn (pos x)          (suc y) = sucn (pos (suc x)) y
  sucn (negsuc 0)       (suc y) = sucn (pos 0) y
  sucn (negsuc (suc x)) (suc y) = sucn (negsuc x) y


  n-n≡0 : ∀ n → n n- n ≡ pos 0
  n-n≡0 0 = refl
  n-n≡0 (suc n) = n-n≡0 n 
  
  z-z≡0 : ∀ z → z z- z ≡ pos 0
  z-z≡0 (pos 0) = refl
  z-z≡0 (pos (suc n)) rewrite z-z≡0 (pos n) = n-n≡0 n
  z-z≡0 (negsuc 0) = refl
  z-z≡0 (negsuc (suc n)) rewrite z-z≡0 (negsuc n) = refl

  0≡z-z : ∀ z → pos 0 ≡ z z- z
  0≡z-z z = sym (z-z≡0 z)

  z+1≡z[n+1] : ∀ n → pos (n + 1) ≡ pos n z+ pos 1
  z+1≡z[n+1] n = refl

  sucn-n≡1 : ∀ n → suc n n- n ≡ pos 1
  sucn-n≡1 0 = refl
  sucn-n≡1 (suc n) = sucn-n≡1 n

  zucpn-pn≡1 : ∀ n → zuc (pos n) z- pos n ≡ pos 1
  zucpn-pn≡1 0 = refl
  zucpn-pn≡1 (suc n) rewrite zucpn-pn≡1 n = sucn-n≡1 n
