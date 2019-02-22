module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Misc.Base

  -- Big step semantics on AExp.
  data [_,_]⇃_ : AExp → State → ℕ → Set where

    Nat : ∀ {n s} → [ NAT n , s ]⇃ n
    Vrr : ∀ {x s} → [ VAR x , s ]⇃ (get-var x s)
    Pls : ∀ {a b x y s} → [ a , s ]⇃ x → [ b , s ]⇃ y →
                          --------------------------------
                              [ a + b , s ]⇃ (x ℕ+ y)



  A⇃ : ∀ {s} → (a : AExp) → [ a , s ]⇃ (aexe a s)
  A⇃ (NAT n) = Nat
  A⇃ (VAR x) = Vrr
  A⇃ (a + b) = Pls (A⇃ a) (A⇃ b)


  -- Big step semantics on BExp.
  data [_,_]⇂_ : BExp → State → Bool → Set where

    Lit : ∀ {b s} → [ BOOL b , s ]⇂ b
    Not : ∀ {e b s} → [ e , s ]⇂ b →
                  ---------------------
                   [ NOT e , s ]⇂ (! b)
    And : ∀ {e₁ e₂ b₁ b₂ s} → [ e₁ , s ]⇂ b₁ → [ e₂ , s ]⇂ b₂ →
                           ---------------------------------------
                                 [ e₁ AND e₂ , s ]⇂ (b₁ ∧ b₂)
    Lss : ∀ {a₁ a₂ n₁ n₂ s} → [ a₁ , s ]⇃ n₁ → [ a₂ , s ]⇃ n₂ →
                           ---------------------------------------
                                [ a₁ LT a₂ , s ]⇂ (n₁ < n₂)
    

  -- Big step semantics.
  data [_,_]⇓_ : IExp → State → State → Set where
  
    Skip       : ∀ {s} →
                           -----------------
                            [ SKIP , s ]⇓ s


    Assign     : ∀ {x n s} → 
                               -------------------------------------------
                                [ (x ≔ n) , s ]⇓ ((x ≔ (aexe n s)) ∷ s)


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
                             ⟦ s , (x ≔ n) ⟧↦⟦ (x ≔ (aexe n s)) ∷ s , SKIP ⟧


    seqbase : ∀ {s that} →
                            ----------------------------------
                             ⟦ s , SKIP ⋯ that ⟧↦⟦ s , that ⟧


    seqstep : ∀ {this s s' this' that} →         ⟦ s , this ⟧↦⟦ s' , this' ⟧ →
                                           ------------------------------------------
                                            ⟦ s , this ⋯ that ⟧↦⟦ s' , this' ⋯ that ⟧


    iftrue  : ∀ {s b i i'} →                  (bexe b s) ≡ true →
                                     ---------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s , i ⟧


    iffalse : ∀ {s b i i'} →                  (bexe b s) ≡ false →
                                     ----------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' ⟧↦⟦ s , i' ⟧
                                      
    whilefalse   : ∀ {s b c} →           bexe b s ≡ false →
                                  -----------------------------------
                                   ⟦ s , WHILE b DO c ⟧↦⟦ s , SKIP ⟧


    whiletrue   : ∀ {s b c} →                         bexe b s ≡ true →
                                  ---------------------------------------------------
                                   ⟦ s , WHILE b DO c ⟧↦⟦ s , (c ⋯ (WHILE b DO c)) ⟧



  
