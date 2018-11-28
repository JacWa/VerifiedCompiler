module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Stack
  open import Proofs.Expr
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)

 {-- correctness : ∀ {state conf' state'}(eprog : IExp){bsse : [ eprog , state ]↦ state'}{bsss : ⦅ (compile eprog) , (config state $ (pos 0)) ⦆↦ conf'} → state' ≡ (STATE conf')
  correctness SKIP {Skip} {base} = refl
  correctness (x ≔ n) {Assign} {trans (step {defc' = defc'}) _} rewrite defc' = {!!}
--}

  verify : ∀ {conf' state'}(eprog : IExp){bsse : ⟦ ⟦⟧ , eprog ⟧↦⟦ state' , SKIP ⟧}{rsteps :  (compile eprog) ⊢ (config ⟦⟧ $ (pos 0)) ⇒* conf'} → state' ≡ (STATE conf')
  verify SKIP {skip} {refl _} = refl
  verify (x ≔ n) {assign} {refl ()}
