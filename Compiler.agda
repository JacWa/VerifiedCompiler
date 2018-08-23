module Compiler where

  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Data.String.Base
  open import Data.List
  open import Data.Bool
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Agda.Builtin.Equality

-------------------------
-- Variable definition --
-------------------------

  data Var : Set₁ where
    _:=_ : (name : String) → (val : ℕ) → Var

  get-value : (name : String) → List Var → ℕ
  get-value name [] = 0
  get-value name ((x := val) ∷ vs) with primStringEquality name x
  ... | true  = val
  ... | false = get-value name vs

------------------------------
-- Expression-tree language --
------------------------------

  -- definition of Expression-tree Language (ETL)
  data Exp : Set where  
    nat   : ℕ → Exp
    var   : String → Exp
    _+_   : Exp → Exp → Exp


  -- function: execute ETL program
  exe : Exp → List Var → ℕ
  exe (nat n)    _     = n
  exe (var name) state = get-value name state 
  exe (x + y)    state = (exe x state) ℕ+ (exe y state)


--------------------
-- Stack language --
--------------------

  -- definition of Stack, indexed by a natural number representing stack height
  infixr 20 _,_
  data Stack : ℕ → Set where
    $   : Stack 0
    _,_ : ∀ {n} → ℕ → Stack n → Stack (suc n)

  -- definition of instructions that can be used to manipulate stack, indexed by 2 natural numbers representing stack height before and after instruction execution respectively.
  data Inst : ℕ → ℕ → Set where
    loadi : ∀ {h} → ℕ      → Inst h (suc h)
    load  : ∀ {h} → String → Inst h (suc h)
    add   : ∀ {h}           → Inst (suc (suc h)) (suc h)

  -- definition of list of Inst, i.e. a stack program. indexed by two numbers representing
  -- stack height before and after program execution respectively.
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
  exs ((load name) :: xs) env stack            = exs xs env ((get-value name env) , stack)
  exs (add         :: xs) env (y1 , y2 , rest) = exs xs env ((y2 ℕ+ y1)           , rest)

--------------
-- Compiler --
--------------

  -- function: compile ETL to SML
  compile : ∀ {n} → Exp → Path n (suc n)
  compile (nat val)  = (loadi val) :: ─
  compile (var name) = (load name) :: ─
  compile (e1 + e2)  = (compile e1) >> (compile e2) >> (add :: ─)


------------------
-- Verification --
------------------

  -- proof: distributive(?) property of exs and _>>_
  >>-ex : ∀ {x y z}(env : List Var)(s : Stack x)(a : Path x y)(b : Path y z) → exs (a >> b) env s ≡ exs b env (exs a env s)
  >>-ex _ _ ─ b = refl
  >>-ex env s (a :: as) b with a | s
  ... | loadi val | ss             = >>-ex env (val                  , ss) as b
  ... | load name | ss             = >>-ex env ((get-value name env) , ss) as b
  ... | add       | (s1 , s2 , ss) = >>-ex env ((s2 ℕ+ s1)           , ss) as b
  
  -- verification of compiler
  verify : ∀ {n} (exp : Exp)(xs : Stack n)(env : List Var) → (exe exp env) , xs ≡ exs (compile exp) env xs
  verify (nat val)  _ _ = refl
  verify (var name) _ _ = refl
  verify (exp₁ + exp₂) xs env rewrite >>-ex env xs ((compile exp₁) >> (compile exp₂)) (add :: ─) | >>-ex env xs (compile exp₁) (compile exp₂) | sym (verify exp₁ xs env) | sym (verify exp₂ (exe exp₁ env , xs) env) = refl
