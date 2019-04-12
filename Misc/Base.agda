module Misc.Base where

  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality

  open import Data.Integer hiding (_≤_; _≟_) renaming (_+_ to _z+_; suc to zuc)
  open import Relation.Binary
  open import Data.Nat.Base using (_≤_; _≟_)
  open import Data.Bool using (not)
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Relation.Nullary
  open import Data.Empty
  import Level using (zero)

  is_≤_ : ℕ → ℕ → Bool
  is 0 ≤ x             = true
  is (suc y) ≤ 0       = false
  is (suc y) ≤ (suc x) = is y ≤ x

  infixr 20 _×_ _,_
  data _×_ {a} (A B : Set a) : Set a where
    _,_ : (a : A)(b : B) → A × B

  fst : ∀ {a A B} → _×_ {a} A B → A
  fst (x , _) = x

  snd : ∀ {a A B} → _×_ {a} A B → B
  snd (_ , y) = y

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

  s≤→⊥ : ∀ {x} → suc x ≤ x → ⊥
  s≤→⊥ {0} ()
  s≤→⊥ {suc x} (_≤_.s≤s p) = s≤→⊥ p

  s≡≤→⊥ : ∀ {x x'} → suc x ≡ suc x' → suc x' ≤ x → ⊥
  s≡≤→⊥ eq ineq rewrite sym eq = s≤→⊥ ineq

  s≤→¬≡ : ∀ {x x'} → suc x' ≤ x → ¬ x ≡ x'
  s≤→¬≡ {zero} {x'} ()
  s≤→¬≡ {suc x} {zero} (_≤_.s≤s ineq) = λ ()
  s≤→¬≡ {suc x} {suc x'} (_≤_.s≤s ineq) = λ x → s≡≤→⊥ x ineq

  _n-_ : ℕ → ℕ → ℤ
  x       n- 0       = + x
  0       n- (suc y) = ℤ.negsuc y
  (suc x) n- (suc y) = x n- y 

  
  0+z : ∀ z → + 0 z+ z ≡ z
  0+z (+ n) = refl
  0+z (ℤ.negsuc n) = refl

  z+0 : ∀ z → z z+ + 0 ≡ z
  z+0 (+ n) rewrite +0 n = refl
  z+0 (ℤ.negsuc n) = refl

  _z-_ : ℤ → ℤ → ℤ
  x z- (+ 0)       = x
  x z- (+ (suc y)) = x z+ (ℤ.negsuc y)
  x z- (ℤ.negsuc y)    = x z+ (+ (suc y))

  
  z++ : ∀ x y → + (suc (x + y)) ≡ zuc (+ x z+ + y)
  z++ x y = refl

  z+comm : ∀ x y → x z+ y ≡ y z+ x
  z+comm (+ x)    (+ y)    rewrite +comm x y = refl
  z+comm (ℤ.negsuc x) (ℤ.negsuc y) rewrite +comm x y = refl
  z+comm (+ x)    (ℤ.negsuc y) = refl
  z+comm (ℤ.negsuc x) (+ y)    = refl

  neg : ℤ → ℤ
  neg (+ 0)       = + 0
  neg (+ (suc x)) = ℤ.negsuc x
  neg (ℤ.negsuc x)    = + (suc x)

  iz_≤_ : ℤ → ℤ → Bool
  iz (ℤ.negsuc _) ≤ (+ _)    = true
  iz (+ _)    ≤ (ℤ.negsuc _) = false 
  iz (+ x)    ≤ (+ y)    = is x ≤ y
  iz (ℤ.negsuc x) ≤ (ℤ.negsuc y) = is y ≤ x

  data _≤_`ℤ` : Rel ℤ Level.zero where
    -≤+ : ∀ {x y} →                  (ℤ.negsuc x) ≤ (+ y)    `ℤ`
    +≤+ : ∀ {x y} → (p : x ≤ y) → (+ x)    ≤ (+ y)    `ℤ`
    -≤- : ∀ {x y} → (p : y ≤ x) → (ℤ.negsuc x) ≤ (ℤ.negsuc y) `ℤ`
    
  ℤ≤trans : ∀ {x y z} → x ≤ y `ℤ` → y ≤ z `ℤ` → x ≤ z `ℤ`
  ℤ≤trans -≤+     (+≤+ _) = -≤+
  ℤ≤trans (-≤- _) -≤+     = -≤+
  ℤ≤trans (-≤- p) (-≤- q) = -≤- (≤trans q p)
  ℤ≤trans (+≤+ p) (+≤+ q) = +≤+ (≤trans p q)

  _<_`ℤ` : Rel ℤ Level.zero
  (ℤ.negsuc 0)       < y `ℤ` = (+ 0)       ≤ y `ℤ`
  (ℤ.negsuc (suc x)) < y `ℤ` = (ℤ.negsuc x)    ≤ y `ℤ`
  (+ x)          < y `ℤ` = (zuc (+ x)) ≤ y `ℤ`

  ℤ<zuc : ∀ x y → x < y `ℤ` → x < zuc y `ℤ`
  ℤ<zuc (ℤ.negsuc (suc a)) (+ b) p  = -≤+
  ℤ<zuc (ℤ.negsuc 0) (+ b) p  = +≤+ _≤_.z≤n
  ℤ<zuc (+ a) (+ (suc b)) p with p
  ... | +≤+ q = +≤+ (≤s (suc b) q)
  ℤ<zuc (ℤ.negsuc (suc (suc n))) (ℤ.negsuc (suc x)) p with p
  ... | -≤- (_≤_.s≤s q) = -≤- (≤s n q)
  ℤ<zuc (ℤ.negsuc (suc n)) (ℤ.negsuc 0) p = -≤+
  
  ℤ<zuc (ℤ.negsuc 1) (ℤ.negsuc (suc n)) (-≤- ())
  ℤ<zuc (+ n) (+ 0) (+≤+ ())
  ℤ<zuc (+ n) (ℤ.negsuc x) ()
  ℤ<zuc (ℤ.negsuc 0) (ℤ.negsuc n) ()

  +-zuc : ∀ x z → + (suc x) z+ ℤ.negsuc z ≡ zuc (+ x z+ ℤ.negsuc z)
  +-zuc 0 0 = refl
  +-zuc 0 (suc n) = refl
  +-zuc (suc x) 0 = refl
  +-zuc (suc x) (suc z) = +-zuc x z

  ℤ<+ : ∀ {x y z} → (+ 0) ≤ x `ℤ` → y < z `ℤ` → y < (x z+ z) `ℤ`
  ℤ<+ {+ 0} {z = z} p q rewrite 0+z z = q
  ℤ<+ {+ (suc n)} {y} {+ z} p q = ℤ<zuc y (+ (n + z)) (ℤ<+ (+≤+ _≤_.z≤n) q)
  ℤ<+ {+ (suc x)} {ℤ.negsuc (suc y)} {ℤ.negsuc z} p q rewrite +-zuc x z = ℤ<zuc (ℤ.negsuc (suc y)) (+ x z+ ℤ.negsuc z) (ℤ<+ {+ x} {ℤ.negsuc (suc y)} {ℤ.negsuc z} (+≤+ _≤_.z≤n) q)
  ℤ<+ {ℤ.negsuc n} ()
  ℤ<+ {_} {ℤ.negsuc 0} {ℤ.negsuc z} _ ()
  ℤ<+ {_} {+ y} {ℤ.negsuc z} _ ()

  ℤ<+s : ∀ {x y z} → (+ 0) ≤ x `ℤ` → y < z `ℤ` → y < (z z+ x) `ℤ`
  ℤ<+s {x} {y} {z} p q rewrite z+comm z x = ℤ<+ p q
  
  data _ℤ≡_ : Rel ℤ Level.zero where
    ℤzero : (+ 0) ℤ≡ (+ 0)
    ℤ+  : ∀ {x y} → (+ x) ℤ≡ (+ y) → (+ (suc x)) ℤ≡ (+ (suc y))
    ℤnero : (ℤ.negsuc 0) ℤ≡ (ℤ.negsuc 0)
    ℤneg  : ∀ {x y} → (ℤ.negsuc x) ℤ≡ (ℤ.negsuc y)

  

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
  sucn (+ x)          (suc y) = sucn (+ (suc x)) y
  sucn (ℤ.negsuc 0)       (suc y) = sucn (+ 0) y
  sucn (ℤ.negsuc (suc x)) (suc y) = sucn (ℤ.negsuc x) y


  n-n≡0 : ∀ n → n ⊖ n ≡ + 0
  n-n≡0 0 = refl
  n-n≡0 (suc n) = n-n≡0 n 
  
  z-z≡0 : ∀ z → z z- z ≡ + 0
  z-z≡0 (+ 0) = refl
  z-z≡0 (+ (suc n)) rewrite z-z≡0 (+ n) = n-n≡0 n
  z-z≡0 (ℤ.negsuc 0) = refl
  z-z≡0 (ℤ.negsuc (suc n)) rewrite z-z≡0 (ℤ.negsuc n) = refl

  0≡z-z : ∀ z → + 0 ≡ z z- z
  0≡z-z z = sym (z-z≡0 z)

  z+1≡z[n+1] : ∀ n → + (n + 1) ≡ + n z+ + 1
  z+1≡z[n+1] n = refl

  sucn-n≡1 : ∀ n → suc n ⊖ n ≡ + 1
  sucn-n≡1 0 = refl
  sucn-n≡1 (suc n) = sucn-n≡1 n

  zucpn-pn≡1 : ∀ n → (zuc (+ n)) z- (+ n) ≡ + 1
  zucpn-pn≡1 0 = refl
  zucpn-pn≡1 (suc n) rewrite zucpn-pn≡1 n = sucn-n≡1 n

  +≡ : ∀ x y →  + x ≡ + y → x ≡ y
  +≡ x y refl = refl

  suc+ :  ∀ x y → + x ≡ + y → + suc x ≡ + suc y
  suc+ x y refl = refl

  +suc : ∀ x y → + suc x ≡ + suc y → + x ≡ + y
  +suc x y refl = refl


  bool⊥' : true ≡ false → ⊥
  bool⊥' ()

  bool⊥ : false ≡ true → ⊥
  bool⊥ ()

  notfalse : ∀ {b} → not b ≡ false → b ≡ true
  notfalse {false} ()
  notfalse {true} a = refl
