module Lang.Stack where

  -- Data.* files are imported from agda-stdlib
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
  open import Data.Maybe
  open import Proofs.NumProofs
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Misc.Base 
  open import Base.DataStructures
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Agda.Primitive

--------------------
-- Stack language --
--------------------

  -- Have to use stack height difference instead of set stack heights, as jumps make it possible for an instruction to apply to the stack at different heights.

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
  _&_ : Prog → Prog → Prog
  []        & ys = ys
  (x :: xs) & ys = x :: (xs & ys)

  size` : Prog → ℕ
  size` [] = 0
  size` (x :: xs) = suc (size` xs)

  size : Prog → ℤ
  size p = + (size` p)

-----------------
-- SIZE PROOFS --
-----------------

  {-- size`+ : {p : Prog} → 0 ≤ size` p
  size`+ = z≤n

  size+ : ∀ {p n}{eq : n ≡ (size` p)} → size p ℤ≡ (pos n)
  size+ {[]} {0} {refl} = ℤzero
  size+ {x :: xs} {suc n} {refl} = ℤpos (size+ {xs} {n} {refl}) --}

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

  
  _፦_ : Prog → ℤ → Maybe Inst  
  []        ፦ _             = nothing
  _         ፦ (-[1+ _ ])    = nothing
  (i :: is) ፦ (+ 0)       = just i
  (i :: is) ፦ (+ (suc n)) = is ፦ (+ n)

