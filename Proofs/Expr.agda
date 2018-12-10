module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool

  -- Big step semantics.
  data [_,_]⇓_ : IExp → State → State → Set where
  
    Skip       : ∀ {s} →
                           -----------------
                            [ SKIP , s ]⇓ s


    Assign     : ∀ {x n s} → 
                               -------------------------------------------
                                [ (x ≔ n) , s ]⇓ set-var x (aexe n s) s


    Seq        : ∀ {s s' s'' this that} →   [ this , s ]⇓ s' → [ that , s' ]⇓ s'' → 
                                            ------------------------------------------
                                                    [ (this ⋯ that) , s ]⇓ s''


    IfFalse    : ∀ {s t bool this that} →  (bexe bool s) ≡ false → [ that , s ]⇓ t → 
                                           --------------------------------------------
                                             [ (IF bool THEN this ELSE that) , s ]⇓ t


    IfTrue     : ∀ {s t bool this that} → (bexe bool s) ≡ true → [ this , s ]⇓ t →
                                          -------------------------------------------
                                            [ (IF bool THEN this ELSE that) , s ]⇓ t


    WhileFalse : ∀ {s bool this} →         (bexe bool s) ≡ false →
                                        -------------------------------
                                        [ (WHILE bool DO this) , s ]⇓ s


    WhileTrue  : ∀ {s s' s'' bool this} →    (bexe bool s) ≡ true → [ this , s ]⇓ s' → [ (WHILE bool DO this) , s' ]⇓ s'' →
                                             ----------------------------------------------------------------------------------
                                                                     [ (WHILE bool DO this) , s ]⇓ s''

  -- Small step semantics.
  data ⟦_,_⟧↦⟦_,_⟧ : State → IExp → State → IExp → Set where

    assign  : ∀ {x n s} →
                            ---------------------------------------------------
                             ⟦ s , (x ≔ n) ⟧↦⟦ set-var x (aexe n s) s , SKIP ⟧


    seqbase : ∀ {s that} →
                            ----------------------------------
                             ⟦ s , SKIP ⋯ that ⟧↦⟦ s , that ⟧


    seqstep : ∀ {s s' this this' that} →         ⟦ s , this ⟧↦⟦ s' , this' ⟧ →
                                           ------------------------------------------
                                            ⟦ s , this ⋯ that ⟧↦⟦ s' , this' ⋯ that ⟧


    iftrue  : ∀ {s b i i'} →                  (bexe b s) ≡ true →
                                     ---------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s , i ⟧


    iffalse : ∀ {s b i i'} →                  (bexe b s) ≡ false →
                                     ----------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s , i' ⟧


    while   : ∀ {s b c} →                         
                                  -----------------------------------------------------------------------
                                   ⟦ s , WHILE b DO c ⟧↦⟦ s , IF b THEN (c ⋯ (WHILE b DO c)) ELSE SKIP ⟧

{--
    whilefalse   : ∀ {s b c} →           bexe b s ≡ false
                                  -----------------------------------
                                   ⟦ s , WHILE b DO c ⟧↦⟦ s , SKIP ⟧


    whiletrue   : ∀ {s b c} →                         bexe b s ≡ true
                                  ---------------------------------------------------
                                   ⟦ s , WHILE b DO c ⟧↦⟦ s , (c ⋯ (WHILE b DO c)) ⟧

--}


