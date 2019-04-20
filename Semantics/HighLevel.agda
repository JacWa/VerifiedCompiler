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
    
    
