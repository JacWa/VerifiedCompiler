module Lang.Stack where

  -- Data.* files are imported from agda-stdlib
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
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

  data Lem1 : Inst → ℕ → Set where
    loadi : ∀ {h n} → Lem1 (LOADI n)   h
    load  : ∀ {h v} → Lem1 (LOAD v)    h
    add   : ∀ {h}   → Lem1 ADD         (suc (suc h))
    store : ∀ {h v} → Lem1 (STORE v)   (suc h)
    jmp   : ∀ {h z} → Lem1 (JMP z)     h
    jmp<  : ∀ {h z} → Lem1 (JMPLESS z) (suc (suc h))
    jmp≥  : ∀ {h z} → Lem1 (JMPGE z)   (suc (suc h))

  iexe : (i : Inst)(c : Config)(p : Lem1 i (height (stack c))) → Config
  iexe (LOADI n)    (config state stack                  pc) loadi = config state (n , stack) (zuc pc)
  iexe (LOAD name)  (config state stack                  pc) load  = config state ((get-var name state) , stack) (zuc pc)
  iexe ADD          (config state (head , (next , rest)) pc) add   = config state ((next ℕ+ head) , rest) (zuc pc)
  iexe (STORE name) (config state (head , rest)          pc) store = config ((name ≔ head) ∷ state) rest (zuc pc)
  iexe (JMP x)      (config state stack                  pc) jmp   = config state stack (x z+ (zuc pc))
  iexe (JMPLESS x)  (config state (head , (next , rest)) pc) jmp< with (is head ≤ next)
  ... | true                                                       = config state rest (zuc pc) -- if next ≮ head, continue
  ... | false                                                      = config state rest (zuc pc z+ x)      -- if next < head, jump
  iexe (JMPGE x)    (config state (head , (next , rest)) pc) jmp≥ with (is head ≤ next)
  ... | true                                                       = config state rest (zuc pc z+ x)      -- if next ≥ head, jump
  ... | false                                                      = config state rest (zuc pc) -- if next ≱ head, continue
  
  iexe ADD         (config _ (_ , $) _) ()
  iexe (JMPLESS _) (config _ (_ , $) _) ()
  iexe (JMPGE _)   (config _ (_ , $) _) ()
  iexe ADD         (config _ $ _) ()
  iexe (STORE _)   (config _ $ _) ()
  iexe (JMPLESS _) (config _ $ _) ()
  iexe (JMPGE _)   (config _ $ _) ()
  
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
  size p = pos (size` p)

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

  size:: : ∀ i is → size (i :: is) ≡ pos (suc (size` is))
  size:: i is = refl

  size&+ : ∀ p q → size (p & q) ≡ (size p) z+ (size q)
  size&+ [] [] = refl
  size&+ [] (i :: is) = refl
  size&+ (i :: is) [] rewrite z+comm (size is) (pos zero) | +comm (size` is) 0 | &[] {is} = refl
  size&+ (i :: is) (j :: js) rewrite size:: i is | size`&+ {is} {j :: js} = refl

  size`&= : ∀ p q → size` (p & q) ≡ size` p ℕ+ size` q
  size`&= [] q = refl
  size`&= (i :: is) q rewrite size`&= is q = refl

  size`&3= : ∀ p q r → size` (p & q & r) ≡ size` p ℕ+ (size` q ℕ+ size` r)
  size`&3= p q r rewrite sym (size`&= q r) | sym (size`&= p (q & r)) = refl

----------
  
  data Lem2 : ℤ → Prog → Set where
    validPC : {pc : ℤ}{prog : Prog}{GZproof : (pos 0) ≤ pc `ℤ`}{LEproof : pc  < (size prog) `ℤ`} → Lem2 pc prog

  inst : (prog : Prog) → (pc : ℤ) → (lb : (pos 0) ≤ pc `ℤ`)(ub : pc  < (size prog) `ℤ`) → Inst
  inst (i :: is) (pos 0)       _ _             = i
  inst (i :: is) (pos (suc n)) _ (+≤+ (s≤s p)) = inst is (pos n) (+≤+ z≤n) (+≤+ {suc n} {size` is} p)
  inst []        (pos n)       _ (+≤+ ())
  inst _ (negsuc _) ()


  _፦_ : Prog → ℤ → Maybe Inst  
  []        ፦ _             = nothing
  _         ፦ (negsuc _)    = nothing
  (i :: is) ፦ (pos 0)       = just i
  (i :: is) ፦ (pos (suc n)) = is ፦ (pos n)
  
  

  {-- step : (p : Prog)(c : Config){vpc : Lem2 (pc c) p}{vh : Lem1 (inst p (pc c) {vpc}) (height (stack c))} → Config
  step p c {vpc} {vh} = iexe (inst p (pc c) {vpc}) c vh --}

   


{--  (x ∷ xs) & ys [ p ] with p
  ... | refl = x ∷ (xs & ys [ {!!} ]) --}

{-  pc? : ∀ {mh pc} → Prog mh pc → ℕ
  pc? [] = 0
  pc? (x ∷ xs) = 1 ℕ+ pc? xs -}

{-  getI : ∀ {mh x}(pc : ℕ)(p : Prog mh pc) → Inst x
  getI 0 p = {!!} -}

{--  exe : ∀ {x y p} → Prog p → Config x → Config y
  exe (x ∷ xs) (config state stack pc) with (pc? (x ∷ xs))
  ... | .pc = iexe x (config state stack pc)
  ... | _   = exe xs (config state stack pc) --}


{-
  -- definition of instructions that can be used to manipulate stack, indexed by 2 natural numbers representing stack height before and after instruction execution respectively.
  data Inst : ℕ → ℕ → Set where
    loadi : ∀ {h} → ℕ      → Inst h (suc h)
    load  : ∀ {h} → String → Inst h (suc h)
    add   : ∀ {h}           → Inst (suc (suc h)) (suc h)

  -- definition of list of Inst, i.e. a stack program. indexed by two numbers representing stack height before and after program execution respectively.
  infixr 20 _::_
  data Path : ℕ → ℕ → Set where
    ─     : ∀ {x} → Path x x
    _::_  : ∀ {x y z} → Inst x y → Path y z → Path x z

  -- function: join two SML programs
  infixl 20 _>>_
  _>>_ : ∀ {x y z} → Path x y → Path y z → Path x z
  ─         >> l = l                                        
  (x :: xs) >> l = (x :: (xs >> l))

  -- function: execute Stack Machine Language (SML) program
  exs : ∀ {x y} → Path x y → List Var → Stack x → Stack y
  exs ─ _ stack = stack
  exs ((loadi val) :: xs) env stack            = exs xs env (val                  , stack)
  exs ((load name) :: xs) env stack            = exs xs env ((get-var name env) , stack)
  exs (add         :: xs) env (y1 , y2 , rest) = exs xs env ((y2 ℕ+ y1)           , rest)
-}
