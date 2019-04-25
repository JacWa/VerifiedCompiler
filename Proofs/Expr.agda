module Proofs.Expr where

  open import Lang.Expr
  open import Base.DataStructures
  open import Base.Inspect
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat using (_≤_; z≤n; s≤s; _>_)
  open import Misc.Base
  open import Data.Empty
  open import Relation.Nullary
  open import Data.Bool.Properties using (∧-comm)
  open import Proofs.Bool
  open import Proofs.NatProofs
  open import Proofs.Basic
  open import Semantics.HighLevel
  

  getFinalStoreᴴᴸ : ∀ {σ' σ i i' f f'} → ⟦ σ , i , f ⟧↦⟦ σ' , i' , f' ⟧ → State
  getFinalStoreᴴᴸ {σ'} = λ _ → σ'

  skipseqσ : ∀ {σ f σ' f' I} → ⟦ σ , SKIP , f ⟧↦*⟦ σ' , I , f' ⟧ → σ' ≡ σ
  skipseqσ done = refl
  skipseqσ (step (empty ¬prf) rest) = ⊥-elim (¬prf refl)

  skipseqf : ∀ {σ f σ' f' I} → ⟦ σ , SKIP , f ⟧↦*⟦ σ' , I , f' ⟧ → f' ≡ f
  skipseqf done = refl
  skipseqf (step (empty ¬prf) rest) = ⊥-elim (¬prf refl)  

  skipseqI : ∀ {σ f σ' f' I} → ⟦ σ , SKIP , f ⟧↦*⟦ σ' , I , f' ⟧ → I ≡ SKIP
  skipseqI done = refl
  skipseqI (step (empty ¬prf) rest) = ⊥-elim (¬prf refl)

  falsel : ∀ {a b σ} → bexe (a AND b) σ ≡ false → bexe a σ ≡ true → bexe b σ ≡ false
  falsel p1 p2 rewrite p2 = p1

  falser : ∀ {a b σ} → bexe (a AND b) σ ≡ false → bexe b σ ≡ true → bexe a σ ≡ false
  falser {a} {σ = σ} p1 p2 rewrite p2 | ∧-comm (bexe a σ) true = p1


  nofᴴ' : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → σ' ≡ σ
  nofᴴ' (empty x) = refl

  nofᴴ'f : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → f' ≡ 0
  nofᴴ'f (empty x) = refl

  nofᴴ'I : ∀ {σ σ' I I' f'} → ¬ I ≡ SKIP → ⟦ σ , I , 0 ⟧↦⟦ σ' , I' , f' ⟧ → I' ≡ SKIP
  nofᴴ'I ¬p (empty x) = refl

  nofᴴ : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → σ' ≡ σ
  nofᴴ done = refl
  nofᴴ (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴ rest

  nofᴴf : ∀ {σ σ' I I' f'} → ⟦ σ , I , 0 ⟧↦*⟦ σ' , I' , f' ⟧ → f' ≡ 0
  nofᴴf done = refl
  nofᴴf (step x rest) rewrite nofᴴ' x | nofᴴ'f x = nofᴴf rest



  explem1a : ∀ {I σ f σ' I' I''} → ⟦ σ , I , suc f ⟧↦⟦ σ' , I' , f ⟧ → ⟦ σ , I ⋯ I'' , suc f ⟧↦*⟦ σ' , I' ⋯ I'' , f ⟧
  explem1a {SKIP} ()
  explem1a {x₁ ≔ x₂} x = step (seqstep x) done
  explem1a {I ⋯ I₁} x = step (seqstep x) done
  explem1a {IF x₁ THEN I ELSE I₁} x = step (seqstep x) done
  explem1a {WHILE x₁ DO I} x = step (seqstep x) done
{-
  explem1 : ∀ {I σ f σ' I' f' I''} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I ⋯ I'' , f ⟧↦*⟦ σ' , I' ⋯ I'' , f' ⟧
  explem1 done = done
  explem1 {f = 0} sem = ?
  explem1 {x ≔ a} (step assign rest) = step (seqstep assign) (explem1 rest)
  explem1 {P ⋯ Q} (step one rest) = ? --step (seqstep one) (explem1 rest)
  explem1 {IF x₂ THEN I ELSE I₁} (step x x₁) = step (seqstep x) (explem1 x₁)
  explem1 {WHILE x₂ DO I} (step x x₁) = step (seqstep x) (explem1 x₁)
-}
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

  detstepHLI' : ∀ {I σ f f' f'' I' σ' I'' σ''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ'' , I'' , f'' ⟧ → I' ≡ I''
  detstepHLI' {f = zero} (empty x) (empty x₁) = refl
  detstepHLI' {SKIP} {f = suc f} ()
  detstepHLI' {x ≔ a} {f = suc f} assign assign = refl
  detstepHLI' {I ⋯ I₁} {f = suc f} sem1 sem2 with I ≟ SKIP
  detstepHLI' {.SKIP ⋯ I₁} {_} {suc f} seqskip seqskip | yes refl = refl
  detstepHLI' {.SKIP ⋯ I₁} {_} {suc f} seqskip (seqstep ()) | yes refl
  detstepHLI' {.SKIP ⋯ I₁} {_} {suc f} (seqstep ()) _ | yes refl
  detstepHLI' {.SKIP ⋯ I₁} {_} {suc f} seqskip _ | no ¬p = ⊥-elim (¬p refl)
  detstepHLI' {.SKIP ⋯ I₁} {_} {suc f} _ seqskip | no ¬p = ⊥-elim (¬p refl)
  detstepHLI' {I ⋯ I₁} {_} {suc f} (seqstep sem1) (seqstep sem2) | no ¬p rewrite detstepHLI' sem1 sem2 = refl
  detstepHLI' {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iftrue x₂) = refl
  detstepHLI' {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iffalse x₂) rewrite x₁ = ⊥-elim (bool⊥' x₂)
  detstepHLI' {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iftrue x₂) rewrite x₁ = ⊥-elim (bool⊥ x₂)
  detstepHLI' {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iffalse x₂) = refl
  detstepHLI' {WHILE x DO I} {f = suc f} (whilefalse x₁) (whilefalse x₂) = refl
  detstepHLI' {WHILE x DO I} {f = suc f} (whilefalse x₁) (whiletrue x₂) rewrite x₁ = ⊥-elim (bool⊥ x₂)
  detstepHLI' {WHILE x DO I} {f = suc f} (whiletrue x₁) (whilefalse x₂) rewrite x₁ = ⊥-elim (bool⊥' x₂)
  detstepHLI' {WHILE x DO I} {f = suc f} (whiletrue x₁) (whiletrue x₂) = refl
  
  detstepHLf : ∀ {I σ f I' σ' σ'' I'' f' f''} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦⟦ σ'' , I'' , f'' ⟧ → f' ≡ f''
  detstepHLf {f = zero} (empty x) (empty x₁) = refl
  detstepHLf {SKIP} {f = suc f} ()
  detstepHLf {x ≔ a} {f = suc f} assign assign = refl
  detstepHLf {I ⋯ I₁} {f = suc f} sem1 sem2 with I ≟ SKIP
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip seqskip | yes refl = refl  
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip (seqstep ()) | yes refl
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} (seqstep ()) _ | yes refl
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} seqskip _ | no ¬p = ⊥-elim (¬p refl)
  detstepHLf {.SKIP ⋯ I₁} {_} {suc f} _ seqskip | no ¬p = ⊥-elim (¬p refl)
  detstepHLf {I ⋯ I₁} {_} {suc f} (seqstep sem1) (seqstep sem2) | no ¬p = refl
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iftrue x₂) = refl
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iftrue x₁) (iffalse x₂) rewrite x₁ = ⊥-elim (bool⊥' x₂)
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iftrue x₂) rewrite x₁ = ⊥-elim (bool⊥ x₂)
  detstepHLf {IF x THEN I ELSE I₁} {σ} {suc f} (iffalse x₁) (iffalse x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whilefalse x₁) (whilefalse x₂) = refl
  detstepHLf {WHILE x DO I} {f = suc f} (whilefalse x₁) (whiletrue x₂) rewrite x₁ = ⊥-elim (bool⊥ x₂)
  detstepHLf {WHILE x DO I} {f = suc f} (whiletrue x₁) (whilefalse x₂) rewrite x₁ = ⊥-elim (bool⊥' x₂)
  detstepHLf {WHILE x DO I} {f = suc f} (whiletrue x₁) (whiletrue x₂) = refl


  ≔-helper-σ : ∀ {σ f σ' f' x a} → ⟦ σ , x ≔ a , f ⟧↦*⟦ σ' , x ≔ a , f' ⟧ → σ' ≡ σ
  ≔-helper-σ done = refl
  ≔-helper-σ (step (empty x₁) (step (empty x₂) sem)) = ⊥-elim (x₂ refl)
  ≔-helper-σ (step assign (step (empty x₁) sem)) = ⊥-elim (x₁ refl)

  ≔-helper-f : ∀ {σ f σ' f' x a} → ⟦ σ , x ≔ a , f ⟧↦*⟦ σ' , x ≔ a , f' ⟧ → f' ≡ f
  ≔-helper-f done = refl
  ≔-helper-f (step (empty x₁) (step (empty x₂) sem)) = ⊥-elim (x₂ refl)
  ≔-helper-f (step assign (step (empty x₁) sem)) = ⊥-elim (x₁ refl)
{-
  if-helper-σ : ∀ {σ f σ' f' b I I'} → ⟦ σ , IF b THEN I ELSE I' , f ⟧↦*⟦ σ' , IF b THEN I ELSE I' , f' ⟧ → σ' ≡ σ
  if-helper-σ done = refl
  if-helper-σ (step (empty x₁) (step (empty x₂) sem)) = ⊥-elim (x₂ refl)
  if-helper-σ {I = I} (step (iftrue x) sem) with I ≟ SKIP
  if-helper-σ {I = .SKIP} (step (iftrue x) (step (empty x₁) sem)) | yes refl = ⊥-elim (x₁ refl)
  ... | no ¬p    = {!!}
  if-helper-σ (step (iffalse x) sem) = {!!}

  if-helper-f : ∀ {σ f σ' f' b I I'} → ⟦ σ , IF b THEN I ELSE I' , f ⟧↦*⟦ σ' , IF b THEN I ELSE I' , f' ⟧ → f' ≡ f
  if-helper-f done = refl
  if-helper-f (step (empty x₁) (step (empty x₂) sem)) = ⊥-elim (x₂ refl)
--  if-helper-f (step assign (step (empty x₁) sem)) = ⊥-elim (x₁ refl)
-}

  ≤f* : ∀ {σ I f σ' I' f'} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → f' ≤ f
  ≤f* done = ≤=
  ≤f* (step (empty x) done) = z≤n
  ≤f* (step (empty x) (step (empty x₁) sem)) = ⊥-elim (x₁ refl)
  ≤f* (step assign sem) with ≤f* sem
  ... | w = ≤s _ w
  ≤f* (step seqskip sem) with ≤f* sem
  ... | w = ≤s _ w 
  ≤f* (step (seqstep x) sem) with ≤f* sem
  ... | w = ≤s _ w
  ≤f* (step (iftrue x) sem) with ≤f* sem
  ... | w = ≤s _ w
  ≤f* (step (iffalse x) sem) with ≤f* sem
  ... | w = ≤s _ w
  ≤f* (step (whilefalse x) sem) with ≤f* sem
  ... | w = ≤s _ w
  ≤f* (step (whiletrue x) sem) with ≤f* sem
  ... | w = ≤s _ w

  ¬SKIPf : ∀ {σ I σ' I' f f'} → ¬ I ≡ SKIP → ⟦ σ , I , suc f ⟧↦⟦ σ' , I' , f' ⟧ → f' ≡ f
  ¬SKIPf ¬p assign = refl
  ¬SKIPf ¬p seqskip = refl
  ¬SKIPf ¬p (seqstep sem) = refl
  ¬SKIPf ¬p (iftrue x) = refl
  ¬SKIPf ¬p (iffalse x) = refl
  ¬SKIPf ¬p (whilefalse x) = refl
  ¬SKIPf ¬p (whiletrue x) = refl

  ≤f : ∀ {σ I σ' I' f f'} → ⟦ σ , I , f ⟧↦⟦ σ' , I' , f' ⟧ → f' ≤ f
  ≤f {I = I} sem with I ≟ SKIP
  ≤f {I = .SKIP} (empty x) | yes refl = ⊥-elim (x refl)
  ≤f {I = I} {f = zero} (empty x) | no ¬p = z≤n
  ≤f {I = I} {f = suc f} sem | no ¬p rewrite ¬SKIPf ¬p sem = ≤s _ ≤=

  
  explem3-a : ∀ I {σ f σ' I' σ'' I'' f''} → f'' ≤ f → ⟦ σ , I , suc f ⟧↦⟦ σ' , I' , f ⟧ → ⟦ σ , I , suc f ⟧↦*⟦ σ'' , I'' , f'' ⟧ → ⟦ σ' , I' , f ⟧↦*⟦ σ'' , I'' , f'' ⟧
  explem3-a .(_ ≔ _) ineq assign done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(_ ≔ _) ineq assign (step assign full) = full
  explem3-a (this ⋯ that) ineq y (step x full) with this ≟ SKIP
  explem3-a (.SKIP ⋯ that) ineq seqskip (step seqskip full) | yes refl = full
  explem3-a (.SKIP ⋯ that) ineq seqskip (step (seqstep ()) full) | yes refl
  explem3-a (.SKIP ⋯ that) ineq (seqstep ()) (step x full) | yes refl
  ... | no  ¬p  with ¬SKIPf (λ ()) x | detstepHLσ y x
  ... | z | z' rewrite z | z' | detstepHLI' y x = full
  explem3-a .(SKIP ⋯ _) ineq seqskip done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(_ ⋯ _) ineq (seqstep stp) done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(IF _ THEN _ ELSE _) ineq (iftrue x) done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(IF _ THEN _ ELSE _) ineq (iftrue x) (step (iftrue x₁) full) = full
  explem3-a .(IF _ THEN _ ELSE _) ineq (iftrue x) (step (iffalse x₁) full) rewrite x = ⊥-elim (bool⊥' x₁)
  explem3-a .(IF _ THEN _ ELSE _) ineq (iffalse x) done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(IF _ THEN _ ELSE _) ineq (iffalse x) (step (iftrue x₁) full) rewrite x = ⊥-elim (bool⊥ x₁)
  explem3-a .(IF _ THEN _ ELSE _) ineq (iffalse x) (step (iffalse x₁) full) = full
  explem3-a .(WHILE _ DO _) ineq (whilefalse x) done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(WHILE _ DO _) ineq (whilefalse x) (step (whilefalse x₁) full) = full
  explem3-a .(WHILE _ DO _) ineq (whilefalse x) (step (whiletrue x₁) full) rewrite x = ⊥-elim (bool⊥ x₁)
  explem3-a .(WHILE _ DO _) ineq (whiletrue x) done = ⊥-elim (s≤→⊥ ineq)
  explem3-a .(WHILE _ DO _) ineq (whiletrue x) (step (whilefalse x₁) full) rewrite x = ⊥-elim (bool⊥' x₁)
  explem3-a .(WHILE _ DO _) ineq (whiletrue x) (step (whiletrue x₁) full) = full

  explem3 : ∀ {f σ I σ' I' f' σ'' I'' f''} → f' > f'' → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f'' ⟧ → ⟦ σ' , I' , f' ⟧↦*⟦ σ'' , I'' , f'' ⟧
  explem3 ineq done full = full
  explem3 {suc f} {I = I} ineq (step x init) full with I ≟ SKIP
  explem3 {suc f} {I = .SKIP} ineq (step () init) full | yes refl
  ... | no ¬p with ¬SKIPf ¬p x
  ... | z rewrite z = explem3 ineq init (explem3-a I (≤trans (s≤ ineq) (≤f* init)) x full)
  explem3 {zero} ineq init done with ≤trans ineq (≤f* init)
  ... | ()
  explem3 {zero} ineq (step (empty x) init) (step (empty x₁) full) = explem3 ineq init full

  detHLσ : ∀ {σ I f σ' I' f' σ'' I''} → ⟦ σ , I , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I , f ⟧↦*⟦ σ'' , I'' , f' ⟧ → σ'' ≡ σ'
  detHLσ done done = refl
  detHLσ done (step x sem2) with ≤≥= (≤f x) (≤f* sem2)
  detHLσ done (step (empty x) done) | refl = refl
  detHLσ done (step (empty x) (step (empty x₁) sem2)) | refl = ⊥-elim (x₁ refl)
  detHLσ (step x sem2) done with ≤≥= (≤f x) (≤f* sem2)
  detHLσ (step (empty x) done) done | refl = refl
  detHLσ (step (empty x) (step (empty x₁) sem2)) done | refl = ⊥-elim (x₁ refl)
  detHLσ (step x sem1) (step x₁ sem2) rewrite detstepHLσ x x₁ |  detstepHLI' x x₁ | detstepHLf x x₁ = detHLσ sem1 sem2
