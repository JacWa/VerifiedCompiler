module Compiler where

open import Data.Nat.Base
open import NatProofs
open import Agda.Builtin.Equality



data Exp : Set where

  num  : (n : ℕ)     → Exp
  _+ₑ_ : Exp → Exp   → Exp

execₑ : Exp → ℕ
execₑ (num n)     = n
execₑ (e1 +ₑ e2)   = (execₑ e1) + (execₑ e2)

----------------------------------------------------------------------
{-
data Stack : Set where

  empty   : Stack
  _push_  : Stack → ℕ → Stack

data StackInst : Set where

  save : ℕ → StackInst
  add  : StackInst → StackInst → StackInst

joinₛ : Stack → Stack → Stack
joinₛ

execₛ : StackInst → Stack
execₛ (save n) = empty push n
execₛ (add a b) = {!execₛ a!}

-}




data Stack : ℕ → Set where
  empty : Stack 0
  push  : ∀ {h} → (n : ℕ) → Stack h → Stack (suc h)

pop : ∀ {n} → Stack (suc n) → ℕ
pop (push x xs) = x

data StackInst : ℕ → ℕ → Set where
  save : {n : ℕ} → ℕ → StackInst n (suc n)
  add  : {n : ℕ} → StackInst (suc (suc n)) (suc n)

infixr 20 _::_
data Path : ℕ → ℕ → Set where
  []   : ∀ {x} → Path x x
  _::_ : ∀ {x y z} → StackInst x y → Path y z → Path x z

infixl 20 _join_
_join_ : ∀ {x y z} → Path x y → Path y z → Path x z
[] join a = a
(x :: xs) join ys = x :: (xs join ys)

-- reverse? prove things about join?

execₛ : ∀ {x y} → Path x y → Stack x → Stack y
execₛ [] s = s
execₛ (i :: is) s with i 
... | save n = execₛ is (push n s)
... | add with s
... | (push n (push m rest)) = execₛ is (push (n + m) rest)

compile : ∀ {x} → Exp → Path x (1 + x) --this keeps the fact that any expression can only result in a stack sized 1 larger than the beginning, and isolates it to be only a feature of Exp compilation, not the SML overall
compile (num n) = (save n) :: []
compile (e1 +ₑ e2) = (compile e2) join (compile e1) join (add :: [])

help1 : (e1 e2 : Exp) → execₛ ((compile e2) join (compile e1) join (add :: [])) empty ≡ execₛ ((compile e1) join (add :: [])) (execₛ (compile e2) empty)
help1 a (num m) = refl
help1 a (b +ₑ c) = {!!}


verify : (exp : Exp) → push (execₑ exp) empty ≡ execₛ (compile exp) empty
verify (num n) = refl
verify ((num n) +ₑ (num m)) = refl
verify ((num n) +ₑ e2) = {!!}
verify (e1 +ₑ (num n)) = {!!}
verify (e1 +ₑ e2) rewrite help1 e1 e2 = {!!}
{-
----------------------------------------------------------------

--TODO: Compiler, Verify

append : ∀ {h₁ h₂} → StackProg h₁ → StackProg h₂ → StackProg (h₂ + h₁)
append p start    = p
append p (is , i) with i
... | add    = (append p is) , add
... | save n = (append p is) , (save n)



compile : {a : ℕ} → Exp → StackProg a
compile (num n) = start , save n



-- verify : ∀ {prog : Exp} → ((execₑ prog) push empty) ≡ execₛ (compile prog)

-}
