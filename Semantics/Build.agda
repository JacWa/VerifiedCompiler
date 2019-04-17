module Semantics.Build where

  
  open import Agda.Builtin.Sigma using (fst; snd) renaming (_,_ to _∣_)
  open import Agda.Builtin.Equality
  open import Base.DataStructures renaming (_,_ to _::_)
  open import Base.Existential
  open import Base.Inspect
  open import Base.Tuple
  
  
  open import Data.Nat using (suc; _≤_) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_) renaming (_+_ to _ℤ+_; suc to zuc)
  open import Data.Empty
  open import Data.Bool using (true; false)

  open import Proofs.Expr

  open import Relation.Nullary

  open import Lang.Expr

  makeHLstp : ∀ I {σ f} → ¬ I ≡ SKIP → ∃[ x ] ⟦ σ , I , suc f ⟧↦⟦ l x , r x , f ⟧
  makeHLstp SKIP {σ} ¬p = ⊥-elim (¬p refl)
  makeHLstp (x ≔ a) {σ} ¬p = (((x ≔ aexe a σ) ∷ σ) , SKIP) ∣ assign
  makeHLstp (I ⋯ I') {σ} {f} _ with I ≟ SKIP
  ... | yes refl = (σ , I') ∣ seqskip
  ... | no ¬p with makeHLstp I {σ} {f} ¬p
  ... | pr ∣ sem = (l pr , r pr ⋯ I') ∣ (seqstep sem)
  makeHLstp (IF x THEN I ELSE I₁) {σ} ¬p with inspect (bexe x σ)
  ... | true with≡ prf = (σ , I) ∣ iftrue prf
  ... | false with≡ prf = (σ , I₁) ∣ iffalse prf
  makeHLstp (WHILE x DO I) {σ} ¬p with inspect (bexe x σ)
  ... | true with≡ prf = (σ , I ⋯ (WHILE x DO I)) ∣ whiletrue prf
  ... | false with≡ prf = (σ , SKIP) ∣ whilefalse prf

  makeHL : ∀ I {σ f} → ∃[ x ] ⟦ σ , I , f ⟧↦*⟦ l x , SKIP , r x ⟧
  makeHL I {σ} {0} with I ≟ SKIP
  ... | yes refl = σ , 0 ∣ done
  ... | no ¬p = σ , 0 ∣ (step (empty ¬p) done)
  makeHL SKIP {σ} {f} = (σ , f) ∣ done
  makeHL (x ≔ a) {σ} {suc f} = (((x ≔ aexe a σ) ∷ σ) , f) ∣ step assign done
  makeHL (I ⋯ I') {σ} {suc f} with I ≟ SKIP
  ... | yes refl with makeHL I' {σ} {f}
  ... | pr ∣ sem = (l pr , r pr) ∣ (step seqskip sem)
  makeHL (I ⋯ I') {σ} {suc f} | no ¬p with makeHLstp I {σ} {f} ¬p
  ... | pr₁ ∣ sem₁ with makeHL (r pr₁ ⋯ I') {l pr₁} {f}
  ... | pr ∣ sem = (l pr) , (r pr) ∣ (step (seqstep sem₁) sem)
  makeHL (IF x THEN I ELSE I') {σ} {suc f} with inspect (bexe x σ)
  ... | true with≡ prf with makeHL I {σ} {f}
  ... | pr ∣ sem = l pr , r pr ∣ (step (iftrue prf) sem)
  makeHL (IF x THEN I ELSE I') {σ} {suc f} | false with≡ prf with makeHL I' {σ} {f}
  ... | pr ∣ sem = l pr , r pr ∣ (step (iffalse prf) sem)
  makeHL (WHILE x DO I) {σ} {suc f} with inspect (bexe x σ)
  ... | false with≡ prf = (σ , f) ∣ (step (whilefalse prf) done)
  ... | true with≡ prf with makeHL (I ⋯ (WHILE x DO I)) {σ} {f}
  ... | pr ∣ sem = l pr , r pr ∣ (step (whiletrue prf) sem)
