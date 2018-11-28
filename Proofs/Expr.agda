module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool

  data [_,_]↦_ : IExp → State → State → Set where
    Skip       : ∀ {s} → [ SKIP , s ]↦ s
    Assign     : ∀ {x n s} → [ (x ≔ n) , s ]↦ (set-var x (aexe n s) s)
    Seq        : ∀ {s1 s2 s3 this that} → [ this , s1 ]↦ s2 → [ that , s2 ]↦ s3 → [ (this ⋯ that) , s1 ]↦ s3
    IfFalse    : ∀ {s t bool this that}{p : (bexe bool s) ≡ false} → [ that , s ]↦ t → [ (IF bool THEN this ELSE that) , s ]↦ t
    IfTrue     : ∀ {s t bool this that}{p : (bexe bool s) ≡ true}  → [ this , s ]↦ t → [ (IF bool THEN this ELSE that) , s ]↦ t
    WhileFalse : ∀ {s bool this}{p : (bexe bool s) ≡ false} → [ (WHILE bool DO this) , s ]↦ s
    WhileTrue  : ∀ {s1 s2 s3 bool this}{p : (bexe bool s1) ≡ true} → (first : [ this , s1 ]↦ s2) → (then : [ (WHILE bool DO this) , s2 ]↦ s3) → [ (WHILE bool DO this) , s1 ]↦ s3

  data ⟦_,_⟧↦⟦_,_⟧ : State → IExp → State → IExp → Set where
    skip : ∀ {s} → ⟦ s , SKIP ⟧↦⟦ s , SKIP ⟧ -- ?
    assign : ∀ {x n s} → ⟦ s , x ≔ n ⟧↦⟦ set-var x (aexe n s) s , SKIP ⟧
    seqbase : ∀ {s s' then} → ⟦ s , then ⟧↦⟦ s' , SKIP ⟧  → ⟦ s , SKIP ⋯ then ⟧↦⟦ s' , SKIP ⟧
    seqstep : ∀ {s s' s'' first then} → ⟦ s , first ⟧↦⟦ s' , SKIP ⟧ → ⟦ s' , SKIP ⋯ then ⟧↦⟦ s'' , SKIP ⟧ → ⟦ s , first ⋯ then ⟧↦⟦ s'' , SKIP ⟧
    iftrue : ∀ {s s' b i i'}{p : (bexe b s) ≡ true} → ⟦ s , i ⟧↦⟦ s' , SKIP ⟧ → ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s' , SKIP ⟧
    iffalse : ∀ {s s' b i i'}{p : (bexe b s) ≡ false} → ⟦ s , i' ⟧↦⟦ s' , SKIP ⟧ → ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s' , SKIP ⟧
    whiletrue : ∀ {s s' b c}{p : (bexe b s) ≡ true} → ⟦ s , c ⋯ (WHILE b DO c) ⟧↦⟦ s' , SKIP ⟧ → ⟦ s , WHILE b DO c ⟧↦⟦ s' , SKIP ⟧
    whilefalse : ∀ {s b c}{p : (bexe b s) ≡ false} → ⟦ s , WHILE b DO c ⟧↦⟦ s , SKIP ⟧
