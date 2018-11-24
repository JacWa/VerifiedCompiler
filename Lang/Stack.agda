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

  data Inst : Set where
    LOADI   : ℕ → Inst
    LOAD    : String → Inst
    ADD     : Inst
    STORE   : String → Inst
    JMP     : ℤ → Inst
    JMPLESS : ℤ → Inst
    JMPGE   : ℤ → Inst

  data Lem1 : Inst → ℕ → Set where
    loadi : ∀ {n h} → Lem1 (LOADI n)   h
    load  : ∀ {v h} → Lem1 (LOAD v)    h
    add   : ∀ {h}   → Lem1 ADD         (suc (suc h))
    store : ∀ {v h} → Lem1 (STORE v)   (suc h)
    jmp   : ∀ {z h} → Lem1 (JMP z)     h
    jmp<  : ∀ {z h} → Lem1 (JMPLESS z) (suc (suc h))
    jmp≥  : ∀ {z h} → Lem1 (JMPGE z)   (suc (suc h))

  iexe : (i : Inst)(c : Config)(p : Lem1 i (height (stack c))) → Config
  iexe (LOADI n)    (config state stack pc)                  loadi = config state (n , stack) (zuc pc)
  iexe (LOAD name)  (config state stack pc)                  load  = config state ((get-var name state) , stack) (zuc pc)
  iexe ADD          (config state (head , (next , rest)) pc) add   = config state ((head ℕ+ next) , rest) (zuc pc)
  iexe (STORE name) (config state (head , rest) pc)          store = config (set-var name head state) rest (zuc pc)
  iexe (JMP x)      (config state stack pc)                  jmp   = config state stack (zuc pc z+ x)
  iexe (JMPLESS x)  (config state (head , (next , rest)) pc) jmp< with (is head ≤ next)
  ... | true                                                       = config state (head , (next , rest)) (zuc pc) -- if next ≮ head, continue
  ... | false                                                      = config state (head , (next , rest)) (zuc pc z+ x)      -- if next < head, jump
  iexe (JMPGE x)    (config state (head , (next , rest)) pc) jmp≥ with (is head ≤ next)
  ... | true                                                       = config state (head , (next , rest)) (zuc pc z+ x)      -- if next ≥ head, jump
  ... | false                                                      = config state (head , (next , rest)) (zuc pc) -- if next ≱ head, continue
  
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

  size : Prog → ℤ
  size [] = pos 0
  size (x :: xs) = zuc (size xs)

{--
  _!n_ : Prog → (pc : ℕ) → Prog
  p         !n 0       = p
  (p :: ps) !n (suc n) = ps !n n
  []        !n (suc n) = NOTHING :: []


  _!_ : Prog → (pc : ℤ) → Prog
  p ! (negsuc _ ) = NOTHING :: []
  p ! (pos x)     = p !n x
--}
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
