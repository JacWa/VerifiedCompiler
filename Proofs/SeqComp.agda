module Proofs.SeqComp where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to _∣_)
  open import Agda.Builtin.Bool

  open import Data.Empty
  open import Relation.Nullary

  open import Proofs.Expr
  open import Proofs.Bool

  open import Lang.Expr
  open import Lang.Stack

  open import Semantics.LowLevel
  open import Semantics.HighLevel
  open import Semantics.Build

  open import Base.Existential
  open import Base.Tuple
  open import Base.DataStructures using (_≔_; _∷_)
  open import Base.Inspect
  open import Base.Or

  open import Data.Nat using (suc)


  ifEnough : ∀ I I' f σ → (∃[ σ' ] ⟦ σ , I , f ⟧↦*⟦ σ' , SKIP , 0 ⟧) ∨ (∃[ x ] ⟦ σ , I ⋯ I' , f ⟧↦*⟦ l x , I' , r x ⟧)
  ifEnough I I' 0       σ with I ≟ SKIP
  ... | yes refl                              = left (σ ∣ done)
  ... | no ¬p                                 = left (σ ∣ (step (empty (¬p)) done))
  ifEnough SKIP                  I' (suc f) σ = right ((σ , f) ∣ (step seqskip done))
  ifEnough (x ≔ a)              I' (suc f) σ with ifEnough SKIP I' f ((x ≔ aexe a σ) ∷ σ)
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep assign) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (assign) rest))
  ifEnough (IF x THEN I ELSE I₁) I' (suc f) σ with inspect (bexe x σ)
  ifEnough (IF x THEN I ELSE I₁) I' (suc f) σ | true with≡ prf with ifEnough I I' f σ
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep (iftrue prf)) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (iftrue prf) rest))
  ifEnough (IF x THEN I ELSE I₁) I' (suc f) σ | false with≡ prf with ifEnough I₁ I' f σ
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep (iffalse prf)) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (iffalse prf) rest))
  ifEnough (WHILE x DO I)        I' (suc f) σ with inspect (bexe x σ)
  ... | true with≡ prf with ifEnough (I ⋯ (WHILE x DO I)) I' f σ
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep (whiletrue prf)) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (whiletrue prf) rest))  
  ifEnough (WHILE x DO I)        I' (suc f) σ | false with≡ prf with ifEnough SKIP I' f σ
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep (whilefalse prf)) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (whilefalse prf) rest))

  ifEnough (I ⋯ I') I'' (suc f) σ with I ≟ SKIP
  ifEnough (I ⋯ I') I'' (suc f) σ | yes refl with ifEnough I' I'' f σ
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep seqskip) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (seqskip) rest))
  ifEnough (I ⋯ I') I'' (suc f) σ | no  ¬p with makeHLstp (I) {σ} {f} ¬p
  ... | (σ* , I*) ∣ stp with ifEnough (I* ⋯ I') I'' f σ*
  ... | right (final ∣ rest) = right (final ∣ (step (seqstep (seqstep stp)) rest))
  ... | left  (σ'    ∣ rest) = left  (σ'    ∣ (step (seqstep stp) rest))

  splitseqHL : ∀ I I' f {σ σ' σ'' f'} → ⟦ σ , I ⋯ I' , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I ⋯ I' , f ⟧↦*⟦ σ'' , SKIP , 0 ⟧ 
                                        ----------------------------------------------------------------------------------------
                                                      → ∃[ x ] ⟦ l x , I' , r x ⟧↦*⟦ σ'' , SKIP , 0 ⟧
                                                      
  splitseqHL I I' 0 {σ'' = σ''} (step (empty x) init) full with I' ≟ SKIP
  ... | yes refl = (σ'' , 0) ∣ done
  ... | no ¬p    = ⊥-elim (¬p (skipseqI init))
  splitseqHL SKIP I' (suc f) init (step {σ} seqskip full) = σ , f ∣ full
  splitseqHL SKIP I' (suc f) init (step (seqstep ()) full)
  splitseqHL (x ≔ a) I' (suc f) {σ} (step (seqstep assign) init) (step (seqstep assign) full) = splitseqHL SKIP I' f init full
  splitseqHL (I ⋯ I₁) I' (suc f) {σ} (step (seqstep x₁) init) (step (seqstep {this' = I₂} x) full) rewrite detstepHLσ x₁ x | detstepHLI' x₁ x = splitseqHL I₂ I' f init full
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} init full with inspect (bexe x σ)
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iftrue x₂)) init) (step (seqstep (iftrue x₁)) full) | true with≡ prf = splitseqHL I I' f init full
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iffalse x₁)) init) full | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} init (step (seqstep (iffalse x₁)) full) | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} init (step (seqstep (iftrue x₁)) full) | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iftrue x₁)) init) full | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iffalse x₂)) init) (step (seqstep (iffalse x₁)) full) | false with≡ prf = splitseqHL I₁ I' f init full
  splitseqHL (WHILE x DO I) I' (suc f) {σ} init full with inspect (bexe x σ)
  splitseqHL (WHILE x DO I) I' (suc f) {σ} init (step (seqstep (whilefalse x₁)) full) | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whilefalse x₁)) init) full | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whiletrue x₁')) init) (step (seqstep (whiletrue x₁)) full)  | true with≡ prf = splitseqHL (I ⋯ (WHILE x DO I)) I' f init full
  splitseqHL (WHILE x DO I) I' (suc f) {σ} init (step (seqstep (whiletrue x₁)) full) | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whiletrue x₁)) init) full | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whilefalse _)) init) (step (seqstep (whilefalse x₁)) full) | false with≡ prf = splitseqHL SKIP I' f init full


  splitseqHL' : ∀ I I' f {σ σ' σ'' f'} → ⟦ σ , I ⋯ I' , f ⟧↦*⟦ σ' , I' , f' ⟧ → ⟦ σ , I ⋯ I' , f ⟧↦*⟦ σ'' , SKIP , 0 ⟧ 
                                        ----------------------------------------------------------------------------------------
                                                      → ⟦ σ' , I' , f' ⟧↦*⟦ σ'' , SKIP , 0 ⟧
                                                      
  splitseqHL' I I' 0 {σ'' = σ''} (step (empty x) init) full with I' ≟ SKIP
  splitseqHL' I I' 0 {σ'' = σ''} (step (empty x) init) (step (empty x') full) | yes refl rewrite skipseqσ full | skipseqσ init | skipseqf init = done
  ... | no ¬p    = ⊥-elim (¬p (skipseqI init))
  splitseqHL' SKIP SKIP (suc f) (step seqskip init) (step {σ} seqskip full) rewrite skipseqσ full | skipseqσ init | skipseqf init | skipseqf full = done
  splitseqHL' SKIP (x ≔ a) (suc f) (step seqskip init) (step {σ} seqskip full) rewrite ≔-helper-σ init | ≔-helper-f init = full
  splitseqHL' SKIP (I' ⋯ I'') (suc f) {f' = 0} (step seqskip init) (step {σ} seqskip full) rewrite detHLσ init full = step (empty (λ ())) done
  splitseqHL' SKIP (I' ⋯ I'') (suc f) {f' = suc f'} (step seqskip init) (step {σ} seqskip full) = explem3 (Data.Nat.s≤s Data.Nat.z≤n) init full
  splitseqHL' SKIP (IF x THEN I' ELSE I'') (suc f) {f' = 0}(step seqskip init) (step {σ} seqskip full) rewrite detHLσ init full = step (empty (λ ())) done
  splitseqHL' SKIP (IF x THEN I' ELSE I'') (suc f) {f' = suc f'}(step seqskip init) (step {σ} seqskip full) = explem3 (Data.Nat.s≤s Data.Nat.z≤n) init full
  splitseqHL' SKIP (WHILE x DO I') (suc f) {f' = 0} (step seqskip init) (step {σ} seqskip full) rewrite detHLσ init full = step (empty (λ ())) done
  splitseqHL' SKIP (WHILE x DO I') (suc f) {f' = suc f'} (step seqskip init) (step {σ} seqskip full) = explem3 (Data.Nat.s≤s Data.Nat.z≤n) init full
  splitseqHL' SKIP I' (suc f) (step (seqstep ()) init)
  splitseqHL' SKIP I' (suc f) init (step (seqstep ()) full)
  splitseqHL' (x ≔ a) I' (suc f) {σ} (step (seqstep assign) init) (step (seqstep assign) full) = splitseqHL' SKIP I' f init full
  splitseqHL' (I ⋯ I₁) I' (suc f) {σ} (step (seqstep x₁) init) (step (seqstep {this' = I₂} x) full) rewrite detstepHLσ x₁ x | detstepHLI' x₁ x = splitseqHL' I₂ I' f init full
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} init full with inspect (bexe x σ)
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iftrue x₂)) init) (step (seqstep (iftrue x₁)) full) | true with≡ prf = splitseqHL' I I' f init full
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iffalse x₁)) init) full | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} init (step (seqstep (iffalse x₁)) full) | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} init (step (seqstep (iftrue x₁)) full) | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iftrue x₁)) init) full | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL' (IF x THEN I ELSE I₁) I' (suc f) {σ} (step (seqstep (iffalse x₂)) init) (step (seqstep (iffalse x₁)) full) | false with≡ prf = splitseqHL' I₁ I' f init full
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} init full with inspect (bexe x σ)
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} init (step (seqstep (whilefalse x₁)) full) | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whilefalse x₁)) init) full | true with≡ prf rewrite prf = ⊥-elim (bool⊥' x₁)
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whiletrue x₁')) init) (step (seqstep (whiletrue x₁)) full)  | true with≡ prf = splitseqHL' (I ⋯ (WHILE x DO I)) I' f init full
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} init (step (seqstep (whiletrue x₁)) full) | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whiletrue x₁)) init) full | false with≡ prf rewrite prf = ⊥-elim (bool⊥ x₁)
  splitseqHL' (WHILE x DO I) I' (suc f) {σ} (step (seqstep (whilefalse _)) init) (step (seqstep (whilefalse x₁)) full) | false with≡ prf = splitseqHL' SKIP I' f init full


  seqlem2 : ∀ {σ σ' σ'' P Q f} → ⟦ σ , P , f ⟧↦*⟦ σ' , SKIP , 0 ⟧ → ⟦ σ , P ⋯ Q , f ⟧↦*⟦ σ'' , SKIP , 0 ⟧ → σ'' ≡ σ'
  seqlem2 done (step (empty x) done) = refl
  seqlem2 done (step (empty x) (step (empty x₁) rest)) = ⊥-elim (x₁ refl)
  seqlem2 (step (empty x) done) (step (empty x₁) done) = refl
  seqlem2 (step (empty x) done) (step (empty x₁) (step (empty x₂) rest)) = ⊥-elim (x₂ refl)
  seqlem2 (step (empty x) (step (empty x₂) init)) (step (empty x₁) rest) = ⊥-elim (x₂ refl)
  seqlem2 (step x init) (step (seqstep x₁) rest) rewrite detstepHLσ x x₁ | detstepHLI' x x₁ | detstepHLf x x₁ = seqlem2 init rest

{-
  lllem1 : ∀ I I' f σ {s σ''} → (hlsem : ∃[ σ' ] ⟦ σ , I , f ⟧↦*⟦ σ' , SKIP , 0 ⟧) → (ifEnough I I' f σ) ≡ left (hlsem) → (compile P & compile Q) ⊢⟦ σ , s , (+ 0) , f ⟧⇒*⟦ σ'' , s , 0 ⟧
  lllem1 = {!!}
-}
