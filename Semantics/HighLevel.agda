module Semantics.HighLevel where

  open import Lang.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Equality
  open import Relation.Nullary
  open import Agda.Builtin.Bool

  -----------------------------------------------
  -- Big step semantics on high level commands --
  -----------------------------------------------

  data ⟦_,_,_⟧⇛⟦_,_⟧ : (I : IExp)(σ : Store)(fuel : ℕ)(σ' : Store)(fuel' : ℕ) → Set where

    Empty      : ∀ {I s} → ------------------------------------
                                ⟦ I , s , 0 ⟧⇛⟦ s , 0 ⟧

    Skip       : ∀ {s f} →
                           -----------------------------------
                            ⟦ SKIP , s , suc f ⟧⇛⟦ s , suc f ⟧


    Assign     : ∀ {x n s f} → 
                               ---------------------------------------------------------
                                ⟦ (x ≔ n) , s , suc f ⟧⇛⟦ ((x ≔ (aexe n s)) ∷ s) , f ⟧


    Seq        : ∀ {s s' s'' this that f f' f''} →   ⟦ this , s , suc f ⟧⇛⟦ s' , f' ⟧ → ⟦ that , s' , f' ⟧⇛⟦ s'' , f'' ⟧ → 
                                                      ---------------------------------------------------------------------
                                                               ⟦ (this ⋯ that) , s , suc f ⟧⇛⟦ s'' , f'' ⟧


    IfFalse    : ∀ {s t bool this that f f'} →  (bexe bool s) ≡ false → ⟦ that , s , f ⟧⇛⟦ t , f' ⟧ → 
                                           ----------------------------------------------------------------
                                                ⟦ (IF bool THEN this ELSE that) , s , suc f ⟧⇛⟦ t , f' ⟧


    IfTrue     : ∀ {s t bool this that f f'} →   (bexe bool s) ≡ true → ⟦ this , s , f ⟧⇛⟦ t , f' ⟧ →
                                                ---------------------------------------------------------
                                                ⟦ (IF bool THEN this ELSE that) , s , suc f ⟧⇛⟦ t , f' ⟧

    WhileFalse : ∀ {s bool this f} →         (bexe bool s) ≡ false →
                                        -------------------------------
                                        ⟦ (WHILE bool DO this) , s , suc f ⟧⇛⟦ s , f ⟧


    WhileTrue  : ∀ {s s' s'' bool this f f' f''} →
                 (bexe bool s) ≡ true → ⟦ this , s , f ⟧⇛⟦ s' , f' ⟧ → ⟦ (WHILE bool DO this) , s' , f' ⟧⇛⟦ s'' , f'' ⟧ →
               -------------------------------------------------------------------------------------------------------------
                                                ⟦ (WHILE bool DO this) , s , suc f ⟧⇛⟦ s'' , f'' ⟧

  -- Big step semantics on terminating IMP programs. --
  data ⟦_,_,_⟧↓⟦_,_⟧ : IExp → Store → ℕ → Store → ℕ → Set where
    Ski↓ : ∀ {s f} → ⟦ SKIP , s , suc f ⟧↓⟦ s , suc f ⟧
    Ass↓ : ∀ {x n s f} → ⟦ x ≔ n , s , suc f ⟧↓⟦ (x ≔ aexe n s) ∷ s , f ⟧
    Seq↓ : ∀ {this that s s' s'' f f' f''} → ⟦ this , s , suc f ⟧↓⟦ s' , f' ⟧ → ⟦ that , s' , f' ⟧↓⟦ s'' , f'' ⟧
                                           --------------------------------------------------------------------
                                                      → ⟦ this ⋯ that , s , suc f ⟧↓⟦ s'' , f'' ⟧
    IfF↓ : ∀ {cond this that s s' f f'} →  (bexe cond s) ≡ false → ⟦ that , s , f ⟧↓⟦ s' , f' ⟧ → 
                                       ----------------------------------------------------------------
                                         ⟦ (IF cond THEN this ELSE that) , s , suc f ⟧↓⟦ s' , f' ⟧
    IfT↓ : ∀ {cond this that s s' f f'} →  (bexe cond s) ≡ true → ⟦ this , s , f ⟧↓⟦ s' , f' ⟧ → 
                                       ----------------------------------------------------------------
                                         ⟦ (IF cond THEN this ELSE that) , s , suc f ⟧↓⟦ s' , f' ⟧
    WhF↓ : ∀ {this cond s f} →                      (bexe cond s) ≡ false →
                                        ------------------------------------------------
                                         ⟦ (WHILE cond DO this) , s , suc f ⟧↓⟦ s , f ⟧            
    WhT↓ : ∀ {this cond s s' s'' f f' f''} →
      (bexe cond s) ≡ true → ⟦ this , s , f ⟧↓⟦ s' , f' ⟧ → ⟦ (WHILE cond DO this) , s' , f' ⟧↓⟦ s'' , f'' ⟧  
   ---------------------------------------------------------------------------------------------------------
                                  →  ⟦ (WHILE cond DO this) , s , suc f ⟧↓⟦ s'' , f'' ⟧   


