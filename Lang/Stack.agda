module Lang.Stack where

  -- Data.* files are imported from agda-stdlib
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
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

  data Inst : {mh : ℕ} → (Diff mh) → Set where
    LOADI   : ℕ → Inst +one
    LOAD    : String → Inst +one
    ADD     : Inst -one'ad
    STORE   : String → Inst -one'st
    JMP     : ℕ → Inst none'nj
    JMPLESS : ℕ → Inst none'cj
    JMPGE   : ℕ → Inst none'cj
    NOTHING : Inst nothing

  
    
  iexe : ∀ {mh x y}{hd : Diff mh}{p1 : mh ≤ x}(p2 : y ≡ (diff x hd {p1})) → Inst hd → Config x → Config y
  iexe refl (LOADI n)    (config state stack pc)                  = config state (n , stack) (suc pc)
  iexe refl (LOAD name)  (config state stack pc)                  = config state ((get-var name state) , stack) (suc pc)
  iexe refl ADD          (config state (head , (next , rest)) pc) = config state ((head ℕ+ next) , rest) (suc pc)
  iexe refl (STORE name) (config state (head , rest) pc)          = config (set-var name head state) rest (suc pc)
  iexe refl (JMP x)      (config state stack pc)                  = config state stack (x)
  iexe refl (JMPLESS x)  (config state (head , (next , rest)) pc) with (is head ≤ next)
  ... | true                                                      = config state (head , (next , rest)) (suc pc) -- if next ≮ head, continue
  ... | false                                                     = config state (head , (next , rest)) (x)      -- if next < head, jump
  iexe refl (JMPGE x)    (config state (head , (next , rest)) pc) with (is head ≤ next)
  ... | true                                                      = config state (head , (next , rest)) (x)      -- if next ≥ head, jump
  ... | false                                                     = config state (head , (next , rest)) (suc pc) -- if next ≱ head, continue
  iexe refl NOTHING      (config state stack pc)               = config state stack (suc pc)
  iexe {2} {1} {p1 = (s≤s ())}
  iexe {2} {0} {p1 = ()}
  iexe {1} {0} {p1 = ()}

  infixr 20 _::_
  data Prog : Set where
    [] : Prog
    _::_ : ∀ {hd}{mh : Diff hd} → Inst mh → Prog → Prog

  infixr 19 _&_
  _&_ : Prog → Prog → Prog
  []        & ys = ys
  (x :: xs) & ys = x :: (xs & ys)

  len : Prog → ℕ
  len [] = 0
  len (x :: xs) = suc (len xs)

  _!_ : Prog → (pc : ℕ) → Prog
  p         ! 0       = p
  (p :: ps) ! (suc n) = ps ! n
  []        ! (suc n) = NOTHING :: []


  data ⦅_,_⦆↦_ {x y : ℕ} : Prog → State → State → Set where
    empty : ∀ {s} → ⦅ [] , s ⦆↦ s
    


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
