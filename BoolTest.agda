module BoolTest where
  open import Agda.Builtin.Equality
  open import Data.Bool.Base renaming (_∧_ to _&_) hiding (_≟_)
  open import Data.Nat.Base hiding (_<_)
  open import Data.Maybe
  open import Relation.Nullary

---------------------
-- Data Structures --
---------------------

  data Stack (A : Set) : Set where
    []   : Stack A
    _::_ : (head : A) → (rest : Stack A) → Stack A

  append : ∀ {A} → Stack A → Stack A → Stack A
  append [] ys        = ys
  append (x :: xs) ys = x :: (append xs ys)

  data Assignment : Set where
    _≔_ : (variable : ℕ) → (value : ℕ) → Assignment

  lt : ℕ → ℕ → Bool
  lt 0 (suc y)       = true
  lt x 0             = false
  lt (suc x) (suc y) = lt x y

  data Config : Set where
    config : (store : Stack Assignment) → (NatStack : Stack ℕ) → (BoolStack : Stack Bool) → (programCounter : ℕ) → Config

  Store : Config → Stack Assignment
  Store (config store _ _ _) = store

  ℕStack : Config → Stack ℕ
  ℕStack (config _ stack _ _) = stack

  BoolStack : Config → Stack Bool
  BoolStack (config _ _ stack _) = stack
  
  PC : Config → ℕ
  PC (config _ _ _ pc) = pc

  get : ℕ → Stack Assignment → ℕ
  get x [] = 0
  get x ((y ≔ n) :: ys) with x ≟ y
  ... | yes _ = n
  ... | no  _ = get x ys 


-------------------------
-- Expression Language --
-------------------------

  data AExp : Set where
    Literal  : ℕ → AExp
    Variable : ℕ → AExp
    _⊹_      : AExp → AExp → AExp

{- Arithmetic Expression execution -}
  aexe : AExp → Stack Assignment → ℕ
  aexe (Literal n) store = n
  aexe (Variable x) store = get x store
  aexe (x ⊹ y) store     = aexe x store + aexe y store


  data BExp : Set where
    Literal : Bool → BExp
    ¬       : BExp → BExp
    _∧_     : BExp → BExp → BExp
    _<_     : AExp → AExp → BExp

{- Boolean Expression execution -}
  bexe : BExp → Stack Assignment → Bool
  bexe (Literal b) store = b
  bexe (¬ b)       store = not (bexe b store)
  bexe (a ∧ b)     store = bexe a store & bexe b store
  bexe (x < y)     store = lt (aexe x store) (aexe y store)


----------------------------
-- Stack Machine Language --
----------------------------

  data Inst : Set where
    LOADIℕ  : ℕ → Inst
    LOADVar  : ℕ → Inst
    ADD      : Inst
    PUSHBool : Bool → Inst
    NOT      : Inst
    AND      : Inst

  exe : Inst → Config → Config
  exe (LOADIℕ n)  (config store ℕstack BoolStack pc) = (config store (n :: ℕstack) BoolStack (suc pc))
  exe (LOADVar x)  (config store ℕstack BoolStack pc) = (config store ((get x store) :: ℕstack) BoolStack (suc pc))
  exe ADD          (config store (hd :: (hd2 :: tl)) BoolStack pc) = (config store ((hd + hd2) :: tl) BoolStack (suc pc))
  exe (PUSHBool b) (config store ℕstack BoolStack pc) = (config store ℕstack (b :: BoolStack) (suc pc))
  exe NOT          (config store ℕstack (hd :: tl) pc) = (config store ℕstack (not hd :: tl) (suc pc))
  exe AND          (config store ℕstack (hd :: (hd2 :: tl)) pc) = (config store ℕstack ((hd & hd2) :: tl) (suc pc))

  _፦_ : (prog : Stack Inst)(pc : ℕ) → Maybe Inst
  (i :: is) ፦ 0  = just i
  []        ፦ pc = nothing
  (i :: is) ፦ (suc pc) = is ፦ pc



{- Big Step Semantics -}
  data _×_⇒_ : Stack Inst → Config → Config → Set where
    exec1 : ∀ {p c} → (i : Inst) → p ፦ (PC c) ≡ just i →
            -----------------------------------------------
                           p × c ⇒ exe i c


  data _×_⇒*_ : Stack Inst → Config → Config → Set where
    terminate : ∀ {p c} → p × c ⇒* c
    step      : ∀ {p c c' c''} → p × c ⇒ c' → p × c' ⇒* c'' →
                --------------------------------------------------
                                 p × c ⇒* c''

-----------------
-- Compilation --
-----------------

  acomp : AExp → Stack Inst
  acomp (Literal n)  = LOADIℕ n :: []
  acomp (Variable x) = LOADVar x :: []
  acomp (x ⊹ y)      = append (acomp x) (append (acomp y) (ADD :: []))

  bcomp : BExp → Stack Inst
  bcomp (Literal b) = PUSHBool b :: []
