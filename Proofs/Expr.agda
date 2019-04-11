module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures 
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Misc.Base
  open import Data.Empty
  open import Relation.Nullary
  open import Data.Bool.Properties using (∧-comm)
  
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
  data ⟦_,_,_⟧↦⟦_,_,_⟧ : State → IExp → ℕ → State → IExp → ℕ → Set where

    empty : ∀ {σ I} → ¬ I ≡ SKIP → ⟦ σ , I , 0 ⟧↦⟦ σ , SKIP , 0 ⟧ 

    assign  : ∀ {x n s f} →
                            ---------------------------------------------------
                             ⟦ s , (x ≔ n) , (suc f) ⟧↦⟦ (x ≔ (aexe n s)) ∷ s , SKIP , f ⟧


    seqskip : ∀ {s that f} →
                            ----------------------------------
                             ⟦ s , SKIP ⋯ that , (suc f) ⟧↦⟦ s , that , f ⟧


    seqstep : ∀ {this s s' this' that f f'} →         ⟦ s , this , f ⟧↦⟦ s' , this' , f' ⟧ →
                                           ---------------------------------------------------
                                            ⟦ s , this ⋯ that , f ⟧↦⟦ s' , this' ⋯ that , f' ⟧


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

    done : ∀ {σ f} → ⟦ σ , SKIP , f ⟧↦*⟦ σ , SKIP , f ⟧
    
    step : ∀ {σ I f σ' I' f' σ'' I'' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ' , I' , f' ⟧↦*⟦ σ'' , I'' , f'' ⟧ →
                                            --------------------------------------------------------------------------
                                                              ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f'' ⟧
    
    
    

  getFinalStoreᴴᴸ : ∀ {σ' σ i i' f f'} → ⟦ σ , i , f ⟧↦⟦ σ' , i' , f' ⟧ → State
  getFinalStoreᴴᴸ {σ'} = λ _ → σ'

  skipseqσ : ∀ {σ f σ' f' I} → ⟦ σ , SKIP , f ⟧↦*⟦ σ' , I , f' ⟧ → σ' ≡ σ
  skipseqσ done = refl
  skipseqσ (step (empty ¬prf) rest) = ⊥-elim (¬prf refl)

  skipseqf : ∀ {σ f σ' f' I} → ⟦ σ , SKIP , f ⟧↦*⟦ σ' , I , f' ⟧ → f' ≡ f
  skipseqf done = refl
  skipseqf (step (empty ¬prf) rest) = ⊥-elim (¬prf refl)

  falsel : ∀ {a b σ} → bexe (a AND b) σ ≡ false → bexe a σ ≡ true → bexe b σ ≡ false
  falsel p1 p2 rewrite p2 = p1

  falser : ∀ {a b σ} → bexe (a AND b) σ ≡ false → bexe b σ ≡ true → bexe a σ ≡ false
  falser {a} {σ = σ} p1 p2 rewrite p2 | ∧-comm (bexe a σ) true = p1


  nofᴴ' : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → σ' ≡ σ
  nofᴴ' (empty x) = refl
  nofᴴ' (seqstep x) = nofᴴ' x

  nofᴴ'f : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → f' ≡ 0
  nofᴴ'f (empty x) = refl
  nofᴴ'f (seqstep x) = nofᴴ'f x

  nofᴴ : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → σ' ≡ σ
  nofᴴ done = refl
  nofᴴ (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴ rest

  nofᴴf : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → f' ≡ 0
  nofᴴf done = refl
  nofᴴf (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴf rest

