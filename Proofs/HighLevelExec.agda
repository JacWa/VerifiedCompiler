module Proofs.HighLevelExec where

  open import Lang.Stack
  open import Lang.Expr renaming (_+_ to _a+_)

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat using (_<_)

  open import Compiler
  
  open import Data.Nat using (suc; ℕ; _≟_) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_; ℤ; _+_) renaming (suc to zuc)
  open import Data.Bool using (true; false)
  open import Data.Maybe using (nothing; just)
  open import Data.Empty

  open import Proofs.NatProofs

  open import Base.DataStructures using (State; Stack; get-var; _≔_; _∷_; hd; tl; _,_; $)
  
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (sym)


  finalPC : Prog → State → Stack → (initialPC : ℤ) → (initialFuel : ℕ) → (finalFuel : ℕ) → ℤ
  finalPC _ _ _ pc 0 _ = pc
  finalPC P σ s pc (suc f) f' with (suc f) ≟ f'
  ... | no _  with P ፦ pc
  ... | nothing          = pc
  ... | just (LOADI x)   = finalPC P σ (x , s) (zuc pc) f f'
  ... | just (LOAD x)    = finalPC P σ (get-var x σ , s) (zuc pc) f f'
  ... | just ADD         = finalPC P σ ((hd s ℕ+ hd (tl s)) , tl (tl s)) (zuc pc) f f'
  ... | just (STORE x)   = finalPC P ((x ≔ (hd s)) ∷ σ) (tl s) (zuc pc) f f'
  ... | just (JMP x)     = finalPC P σ s (zuc pc + x) f f'
  finalPC P σ s pc (suc f) f' | no _ | just (JMPLESS x) with hd (tl s) < hd s
  finalPC P σ s pc (suc f) f' | no _ | just (JMPLESS x) | false = finalPC P σ (tl (tl s)) (zuc pc)     f f'   
  finalPC P σ s pc (suc f) f' | no _ | just (JMPLESS x) | true  = finalPC P σ (tl (tl s)) (zuc pc + x) f f'
  finalPC P σ s pc (suc f) f' | no _ | just (JMPGE x)   with hd (tl s) < hd s
  finalPC P σ s pc (suc f) f' | no _ | just (JMPGE x)   | false = finalPC P σ (tl (tl s)) (zuc pc + x) f f'
  finalPC P σ s pc (suc f) f' | no _ | just (JMPGE x)   | true  = finalPC P σ (tl (tl s)) (zuc pc)     f f'   
  finalPC P σ s pc (suc f) f' | yes _ = pc

  lem1-helper : ∀ {a} {f} → size` (acomp a) ℕ+ f ≡ f → ⊥
  lem1-helper {a} {f} with size` (acomp a) ℕ+ f ≟ f
  lem1-helper {a} {f} | no ¬p = ¬p
  lem1-helper {NAT x} {f} | yes ()
  lem1-helper {VAR x} {f} | yes ()
  lem1-helper {a a+ b} {f} | yes p rewrite size`&+ {acomp a} {acomp b & ADD :: []} | size`&+ {acomp b} {ADD :: []} | +assoc (size` (acomp a)) (size` (acomp b)) 1 | sym (+assoc (size` (acomp a) ℕ+ size` (acomp b)) 1 f) = +suc⊥ (size` (acomp a) ℕ+ size` (acomp b)) f

  postulate
    lem1 : ∀ a f → (size` (acomp a) ℕ+ f ≟ f) ≡ no (lem1-helper {a} {f})

  postulate
    assignPC : ∀ a {f x σ} → finalPC (acomp a & STORE x :: []) σ $ (+ 0) (suc (size` (acomp a) ℕ+ f)) f ≡ + (suc (size` (acomp a)))
{-  assignPC (NAT x) {ℕ.zero} = refl
  assignPC (VAR x) {ℕ.zero} = refl
  assignPC (a a+ b) {ℕ.zero} = {!!}
  assignPC (NAT x) {suc f} = {!!}
  assignPC (VAR x) {suc f} = {!!}
  assignPC (a a+ a₁) {suc f} = {!!}
-}

