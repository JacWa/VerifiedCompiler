module Lang.Stack where

------------------------------------------------------------
-- Definition of the stack machine language instructions, --
-- the construction of programs and some basic proofs     --
-- about the size function for said programs.             --
------------------------------------------------------------

  open import Agda.Builtin.Equality

  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_)
  open import Data.String.Base
  open import Data.Maybe
  
  open import Proofs.NatProofs
  open import Proofs.Basic
  
  open import Misc.Base
  
  open import Base.DataStructures

--------------------
-- Stack language --
--------------------

  data Inst : Set where
    LOADI   : ℕ → Inst
    LOAD    : String → Inst
    ADD     : Inst
    STORE   : String → Inst
    JMP     : ℤ → Inst
    JMPLESS : ℤ → Inst
    JMPGE   : ℤ → Inst
  
  infixr 20 _::_
  data Prog : Set where
    []   : Prog
    _::_ : Inst → Prog → Prog

  infixr 19 _&_
  -- Programs composition.
  _&_ : Prog → Prog → Prog
  []        & ys = ys
  (x :: xs) & ys = x :: (xs & ys)

  -- Instruction lookup / program indexing.
  _፦_ : Prog → ℤ → Maybe Inst  
  []        ፦ _             = nothing
  _         ፦ (-[1+ _ ])    = nothing
  (i :: is) ፦ (+ 0)       = just i
  (i :: is) ፦ (+ (suc n)) = is ፦ (+ n)

  
  size` : Prog → ℕ
  size` [] = 0
  size` (x :: xs) = suc (size` xs)

  size : Prog → ℤ
  size p = + (size` p)

-----------------
-- SIZE PROOFS --
-----------------

  ℕ≤= : ∀ {x} → x ≤ x
  ℕ≤= {0} = z≤n
  ℕ≤= {suc n} = s≤s ℕ≤=

  ℕ≤↓ : ∀ {x y}{s : suc x ≤ suc y} → x ≤ y
  ℕ≤↓ {s = s≤s p} = p

  ℕ≤s : ∀ {x y}{base : x ≤ y} → x ≤ (suc y)
  ℕ≤s {0} = z≤n
  ℕ≤s {suc x} {suc y} {base} = s≤s (ℕ≤s {x} {y} {ℕ≤↓ {s = base}})
  ℕ≤s {suc x} {0} {}

  +sucmv : ∀ {x y} → y ℕ+ suc x ≡ suc y ℕ+ x
  +sucmv {x} {0} = refl
  +sucmv {x} {suc y} rewrite +sucmv {x} {y} = refl
  
  ℕ≤+ : ∀ {x y} → x ≤ y ℕ+ x
  ℕ≤+ {0} {suc y} = z≤n
  ℕ≤+ {x} {0} = ℕ≤=
  ℕ≤+ {suc x} {suc y} rewrite +sucmv {x} {y} = s≤s (ℕ≤s {base = ℕ≤+})

  &[] : ∀ {p} → p & [] ≡ p
  &[] {[]} = refl
  &[] {x :: xs} rewrite &[] {xs} = refl

  suc≡ : ∀ {x y}{base : x ≡ y} → suc x ≡ suc y
  suc≡ {base = refl} = refl

  size`::+ : ∀ {p ps} → suc (size` ps) ≡ size` (p :: ps)
  size`::+ = refl

  size1 : size` (ADD :: []) ≡ 1
  size1 = refl

  size`&+ : ∀ {p q} → size` (p & q) ≡ (size` p ℕ+ size` q)
  size`&+ {[]} = refl
  size`&+ {x :: xs} {q} rewrite size`::+ {x} {xs} | suc≡ {size` (xs & q)} {size` xs ℕ+ size` q} {size`&+ {xs} {q}} = refl

  size`& : ∀ {p q} → (size` q) ≤ (size` (p & q))
  size`& {[]} {q} rewrite &[] {q} = ℕ≤=
  size`& {x :: xs} {q} rewrite size`&+ {x :: xs} {q} = ℕ≤s {base = ℕ≤+}

  size&[] : ∀ {p} → size p ≡ size (p & [])
  size&[] {p} rewrite &[] {p} = refl

  <size&[] : ∀ {p pc} → pc < (size p) `ℤ` ≡ pc < (size (p & [])) `ℤ`
  <size&[] {p} rewrite &[] {p} = refl

  size& : ∀ {p q} → (size q) ≤ (size (p & q)) `ℤ`
  size& {[]} {q} rewrite &[] {q} = +≤+ ℕ≤=
  size& {x :: xs} {q} rewrite size`&+ {x :: xs} {q} = +≤+ (ℕ≤s {base = ℕ≤+})

  size`&2 : ∀ {a b c d} → size` c ≤ size` (a & b & c & d)
  size`&2 {a} {b} {c} {d} rewrite size`&+ {a} {b & c & d} | size`&+ {b} {c & d} | size`&+ {c} {d} | +3free4 (size` a) (size` b) (size` c) (size` d) = ≤+ ≤=

  size`&3 : ∀ {a b c} → size` c ≤ size` (a & b & c)
  size`&3 {a} {b} {c} rewrite size`&+ {a} {b & c} | size`&+ {b} {c} | +comm (size` b) (size` c) | +oswap (size` a) (size` c) (size` b) = ≤+ ≤=

  size:: : ∀ i is → size (i :: is) ≡ + (suc (size` is))
  size:: i is = refl

  size&+ : ∀ p q → size (p & q) ≡ (size p) z+ (size q)
  size&+ [] [] = refl
  size&+ [] (i :: is) = refl
  size&+ (i :: is) [] rewrite z+comm (size is) (+ zero) | +comm (size` is) 0 | &[] {is} = refl
  size&+ (i :: is) (j :: js) rewrite size:: i is | size`&+ {is} {j :: js} = refl

  size`&= : ∀ p q → size` (p & q) ≡ size` p ℕ+ size` q
  size`&= [] q = refl
  size`&= (i :: is) q rewrite size`&= is q = refl

  size`&3= : ∀ p q r → size` (p & q & r) ≡ size` p ℕ+ (size` q ℕ+ size` r)
  size`&3= p q r rewrite sym (size`&= q r) | sym (size`&= p (q & r)) = refl

  size`trans : ∀ P Q → size` (P & Q) ≡ size` (Q & P)
  size`trans P Q rewrite size`&+ {P} {Q} | +comm (size` P) (size` Q) | size`&+ {Q} {P} = refl

  &assoc : ∀ P Q R → P & Q & R ≡ (P & Q) & R
  &assoc [] Q R = refl
  &assoc (i :: is) Q R rewrite &assoc is Q R = refl
  
  size`&+3/4 : ∀ P Q R S → size` (P & Q & R & S) ≡ size` R ℕ+ size` (P & Q & S)
  size`&+3/4 P Q R S rewrite &assoc P Q (R & S) | size`&+ {P & Q} {R & S} | size`&+ {R} {S} | +assoc (size` (P & Q)) (size` R) (size` S) | +comm (size` (P & Q)) (size` R) | sym (+assoc (size` R) (size` (P & Q)) (size` S)) | sym (size`&+ {P & Q} {S}) | &assoc P Q S = refl


