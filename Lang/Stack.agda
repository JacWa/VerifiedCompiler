module Lang.Stack where

  -- Data.* files are imported from agda-stdlib
  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.String.Base
  open import Data.Bool
  open import Proofs.NumProofs
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Misc.Base 
  open import Base.DataStructures

--------------------
-- Stack language --
--------------------

  {-- data δh : Set where
    δh=   : ℤ → δh  --}

  

  data Inst : {mh : ℕ} → (Diff mh) → Set where
    LOADI   : ℕ → Inst +one
    LOAD    : String → Inst +one
    ADD     : Inst -one'ad
    STORE   : String → Inst -one'st
    JMP     : ℕ → Inst none'nj
    JMPLESS : ℕ → Inst none'cj
    JMPGE   : ℕ → Inst none'cj
    
  iexe : ∀ {mh x y}{hd : Diff mh}{p1 : mh ≤ x} → Inst hd → Config x → Config y
  iexe (LOADI n)    (config state stack pc)                  = config state (n , stack) (suc pc)
  iexe (LOAD name)  (config state stack pc)                  = config state ((get-var name state) , stack) (suc pc)
  iexe ADD          (config state (head , (next , rest)) pc) = config state ((head ℕ+ next) , rest) (suc pc)
  iexe (STORE name) (config state (head , rest) pc)          = config (set-var name head state) rest (suc pc)
  iexe (JMP x)      (config state stack pc)                  = config state stack (x)
  iexe (JMPLESS x)  (config state (head , (next , rest)) pc) with (is head ≤ next)
  ...                                                | true  = config state (head , (next , rest)) (suc pc) -- if next ≮ head, continue
  ...                                                | false = config state (head , (next , rest)) (x)      -- if next < head, jump
  iexe refl (JMPGE x)    (config state (head , (next , rest)) pc) with (is head ≤ next)
  ...                                                | true  = config state (head , (next , rest)) (x)      -- if next ≤ head, jump
  ...                                                | false = config state (head , (next , rest)) (suc pc) -- if next ≰ head, continue

 {--  data Prog : ℕ → ℕ → ℕ → Set where
    []   : ∀ {x} → Prog x x 0
    _∷_ : ∀ {x y z p} → Inst x y → Prog y z p → Prog x z (suc p)


  exe : ∀ {x y p} → Prog x y p → Config x → Config y
  exe [] c = c
--}  


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
