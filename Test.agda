module Test where

  open import Compiler
  open import Lang.Expr
  open import Lang.Stack
  open import Agda.Builtin.String


  ex1 : IExp
  ex1 = ("i" ≔ NAT 0) ⋯ (WHILE (VAR "i" LT NAT 5) DO ("i" ≔ (VAR "i" + NAT 1)))

  ex1' : Prog
  ex1' = compile ex1


  record Truth : Set₁ where
  
