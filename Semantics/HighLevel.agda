module Semantics.HighLevel where

  open import Lang.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Agda.Builtin.Equality
  open import Relation.Nullary
  open import Agda.Builtin.Bool

    -- Small step semantics.
  data ⟦_,_,_⟧↦⟦_,_,_⟧ : State → IExp → ℕ → State → IExp → ℕ → Set where

    empty : ∀ {σ I} → ¬ I ≡ SKIP → ⟦ σ , I , 0 ⟧↦⟦ σ , SKIP , 0 ⟧ 

    assign  : ∀ {x n s f} →
                            ---------------------------------------------------
                             ⟦ s , (x ≔ n) , (suc f) ⟧↦⟦ (x ≔ (aexe n s)) ∷ s , SKIP , f ⟧


    seqskip : ∀ {s that f} →
                            ----------------------------------
                             ⟦ s , SKIP ⋯ that , (suc f) ⟧↦⟦ s , that , f ⟧


    seqstep : ∀ {this s s' this' that f} →         ⟦ s , this , suc f ⟧↦⟦ s' , this' , f ⟧ →
                                           ---------------------------------------------------
                                            ⟦ s , this ⋯ that , suc f ⟧↦⟦ s' , this' ⋯ that , f ⟧


    iftrue  : ∀ {s b i i' f} →                  (bexe b s) ≡ true →
                                     ---------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' , suc f ⟧↦⟦ s , i , f ⟧


    iffalse : ∀ {s b i i' f} →                  (bexe b s) ≡ false →
                                     ----------------------------------------
                                      ⟦ s , IF b THEN i ELSE i' , suc f ⟧↦⟦ s , i' , f ⟧
                                      
    whilefalse   : ∀ {s b c f} →           bexe b s ≡ false →
                                  -----------------------------------
                                   ⟦ s , WHILE b DO c , suc f ⟧↦⟦ s , SKIP , f ⟧


    whiletrue   : ∀ {s b c f} →                         bexe b s ≡ true →
                                  ---------------------------------------------------
                                   ⟦ s , WHILE b DO c , suc f ⟧↦⟦ s , (c ⋯ (WHILE b DO c)) , f ⟧



  data ⟦_,_,_⟧↦*⟦_,_,_⟧ : State → IExp → ℕ → State → IExp → ℕ → Set where

    done : ∀ {σ f I} → ⟦ σ , I , f ⟧↦*⟦ σ , I , f ⟧
    
    step : ∀ {σ I f σ' I' f' σ'' I'' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ' , I' , f' ⟧↦*⟦ σ'' , I'' , f'' ⟧ →
                                            --------------------------------------------------------------------------
                                                              ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f'' ⟧
    
    

  -- Big step semantics.
  data ⟦_,_,_⟧⇛⟦_,_⟧ : (I : IExp)(σ : State)(fuel : ℕ)(σ' : State)(fuel' : ℕ) → Set where

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




{-

  
  -- Big step semantics on AExp.
  data ⟦_,_⟧ᴬ⇛_ : AExp → State → ℕ → Set where

    Nat : ∀ {n s} → ⟦ NAT n , s ⟧ᴬ⇛ n
    Vrr : ∀ {x s} → ⟦ VAR x , s ⟧ᴬ⇛ (get-var x s)
    Pls : ∀ {a b x y s} → ⟦ a , s ⟧ᴬ⇛ x → ⟦ b , s ⟧ᴬ⇛ y →
                          --------------------------------
                              ⟦ a + b , s ⟧ᴬ⇛ (x ℕ+ y)



  A⇃ : ∀ {s} → (a : AExp) → ⟦ a , s ⟧ᴬ⇛ (aexe a s)
  A⇃ (NAT n) = Nat
  A⇃ (VAR x) = Vrr
  A⇃ (a + b) = Pls (A⇃ a) (A⇃ b)


  -- Big step semantics on BExp.
  data ⟦_,_⟧ᴮ⇛_ : BExp → State → Bool → Set where

    Lit : ∀ {b s} → ⟦ BOOL b , s ⟧ᴮ⇛ b
    Not : ∀ {e b s} → ⟦ e , s ⟧ᴮ⇛ b →
                  ---------------------
                   ⟦ NOT e , s ⟧ᴮ⇛ (! b)
    And : ∀ {e₁ e₂ b₁ b₂ s} → ⟦ e₁ , s ⟧ᴮ⇛ b₁ → ⟦ e₂ , s ⟧ᴮ⇛ b₂ →
                           ---------------------------------------
                                 ⟦ e₁ AND e₂ , s ⟧ᴮ⇛ (b₁ ∧ b₂)
    Lss : ∀ {a₁ a₂ n₁ n₂ s} → ⟦ a₁ , s ⟧ᴬ⇛ n₁ → ⟦ a₂ , s ⟧ᴬ⇛ n₂ →
                           ---------------------------------------
                                ⟦ a₁ LT a₂ , s ⟧ᴮ⇛ (n₁ < n₂)
    
-}
