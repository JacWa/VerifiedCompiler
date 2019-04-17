module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures
  open import Base.Inspect
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat using (_≤_; z≤n; s≤s)
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

    done : ∀ {σ f I} → ⟦ σ , I , f ⟧↦*⟦ σ , I , f ⟧
    
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

  nofᴴ'I : ∀ {σ σ' I I' f'} → ¬ I ≡ SKIP → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → I' ≡ SKIP
  nofᴴ'I _  (empty x) = refl
  nofᴴ'I ¬p (seqstep x) = {!!}

  nofᴴ : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → σ' ≡ σ
  nofᴴ done = refl
  nofᴴ (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴ rest

  nofᴴf : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → f' ≡ 0
  nofᴴf done = refl
  nofᴴf (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴf rest


  explem1a : ∀ {I σ f σ' I' f' I''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I ⋯ I'' , f ⟧↦*⟦ σ' , I' ⋯ I'' , f' ⟧
  explem1a {SKIP} x = step (seqstep x) done
  explem1a {x₁ ≔ x₂} x = step (seqstep x) done
  explem1a {I ⋯ I₁} x = step (seqstep x) done
  explem1a {IF x₁ THEN I ELSE I₁} x = step (seqstep x) done
  explem1a {WHILE x₁ DO I} x = step (seqstep x) done

  explem1 : ∀ {I σ f σ' I' f' I''} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I ⋯ I'' , f ⟧↦*⟦ σ' , I' ⋯ I'' , f' ⟧
  explem1 done = done
  explem1 {SKIP} (step (empty x) _) = ⊥-elim (x refl)
  explem1 {_ ≔ _} (step (empty x) done) = step (seqstep (empty x)) done
  explem1 {_ ≔ _} (step (empty _) (step (empty x) _)) = ⊥-elim (x refl)
  explem1 {x ≔ a} (step assign rest) = step (seqstep assign) (explem1 rest)
  explem1 {P ⋯ Q} (step one rest) = step (seqstep one) (explem1 rest)
  explem1 {IF x₂ THEN I ELSE I₁} (step x x₁) = step (seqstep x) (explem1 x₁)
  explem1 {WHILE x₂ DO I} (step x x₁) = step (seqstep x) (explem1 x₁)

  explem2a : ∀ {σ I f σ' I' f' σ'' I'' f''} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ' , I' , f' ⟧↦⟦ σ'' , I'' , f'' ⟧ → ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f'' ⟧
  explem2a done stp = step stp done
  explem2a (step one rest) stp = step one (explem2a rest stp)

  explem2 : ∀ {σ I f σ' I' f' σ'' I'' f''} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ' , I' , f' ⟧↦*⟦ σ'' , I'' , f'' ⟧ → ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f'' ⟧
  explem2 x done = x
  explem2 x (step one rest) = explem2 (explem2a x one) rest

  detstepHLσ : ∀ {I σ f I' σ' f' I'' σ'' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ'' , I'' , f'' ⟧ → σ' ≡ σ''
  detstepHLσ {f = zero} sem1 sem2 rewrite nofᴴ' sem1 | nofᴴ' sem2 = refl
  detstepHLσ {SKIP} {f = suc f} ()
  detstepHLσ {x ≔ a} {f = suc f} assign assign = refl
  detstepHLσ {I ⋯ I₁} {f = suc f} sem1 sem2 with I ≟ SKIP
  detstepHLσ {.SKIP ⋯ I₁} {_} {suc f} seqskip seqskip | yes refl = refl
  detstepHLσ {.SKIP ⋯ I₁} {_} {suc f} seqskip (seqstep ()) | yes refl
  detstepHLσ {.SKIP ⋯ I₁} {_} {suc f} (seqstep ()) _ | yes refl
  detstepHLσ {.SKIP ⋯ I₁} {_} {suc f} seqskip _ | no ¬p = ⊥-elim (¬p refl)
  detstepHLσ {.SKIP ⋯ I₁} {_} {suc f} _ seqskip | no ¬p = ⊥-elim (¬p refl)
  detstepHLσ {I ⋯ I₁} {_} {suc f} (seqstep sem1) (seqstep sem2) | no ¬p = detstepHLσ sem1 sem2
  detstepHLσ {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iftrue x₂) = refl
  detstepHLσ {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iffalse x₂) = refl
  detstepHLσ {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iftrue x₂) = refl
  detstepHLσ {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iffalse x₂) = refl
  detstepHLσ {WHILE x DO I} {f = suc f} (whilefalse x₁) (whilefalse x₂) = refl
  detstepHLσ {WHILE x DO I} {f = suc f} (whilefalse x₁) (whiletrue x₂) = refl
  detstepHLσ {WHILE x DO I} {f = suc f} (whiletrue x₁) (whilefalse x₂) = refl
  detstepHLσ {WHILE x DO I} {f = suc f} (whiletrue x₁) (whiletrue x₂) = refl

  detstepHLf : ∀ {I σ f I' σ' f' I'' σ'' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ'' , I'' , f'' ⟧ → f' ≡ f''
  detstepHLf {f = zero} sem1 sem2 rewrite nofᴴ'f sem1 | nofᴴ'f sem2 = refl
  detstepHLf {SKIP} {f = suc f} ()
  detstepHLf {x ≔ a} {f = suc f} assign assign = refl
  detstepHLf {I ⋯ I₁} {f = suc f} sem1 sem2 with I ≟ SKIP
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip seqskip | yes refl = refl
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip (seqstep ()) | yes refl
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} (seqstep ()) _ | yes refl
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip _ | no ¬p = ⊥-elim (¬p refl)
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} _ seqskip | no ¬p = ⊥-elim (¬p refl)
  detstepHLf {I ⋯ I₁} {_} {suc f} (seqstep sem1) (seqstep sem2) | no ¬p = detstepHLf sem1 sem2
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iftrue x₂) = refl
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iffalse x₂) = refl
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iftrue x₂) = refl
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iffalse x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whilefalse x₁) (whilefalse x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whilefalse x₁) (whiletrue x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whiletrue x₁) (whilefalse x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whiletrue x₁) (whiletrue x₂) = refl

  detstepHLI : ∀ {I σ f I' σ' f' I'' σ'' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ'' , I'' , f'' ⟧ → σ' ≡ σ''
  detstepHLI {f = zero} sem1 sem2 = {!!} --rewrite nofᴴ' sem1 | nofᴴ' sem2 = refl
  detstepHLI {SKIP} {f = suc f} ()
  detstepHLI {x ≔ a} {f = suc f} assign assign = refl
  detstepHLI {I ⋯ I₁} {f = suc f} sem1 sem2 with I ≟ SKIP
  detstepHLI {.SKIP ⋯ I₁} {_} {suc f} seqskip seqskip | yes refl = refl
  detstepHLI {.SKIP ⋯ I₁} {_} {suc f} seqskip (seqstep ()) | yes refl
  detstepHLI {.SKIP ⋯ I₁} {_} {suc f} (seqstep ()) _ | yes refl
  detstepHLI {.SKIP ⋯ I₁} {_} {suc f} seqskip _ | no ¬p = ⊥-elim (¬p refl)
  detstepHLI {.SKIP ⋯ I₁} {_} {suc f} _ seqskip | no ¬p = ⊥-elim (¬p refl)
  detstepHLI {I ⋯ I₁} {_} {suc f} (seqstep sem1) (seqstep sem2) | no ¬p = detstepHLI sem1 sem2
