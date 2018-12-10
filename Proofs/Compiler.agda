module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Stack
  open import Proofs.Expr
  open import Proofs.NatProofs
  open import Misc.Base
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat.Base

 {-- correctness : ∀ {state conf' state'}(eprog : IExp){bsse : [ eprog , state ]↦ state'}{bsss : ⦅ (compile eprog) , (config state $ (pos 0)) ⦆↦ conf'} → state' ≡ (STATE conf')
  correctness SKIP {Skip} {base} = refl
  correctness (x ≔ n) {Assign} {trans (step {defc' = defc'}) _} rewrite defc' = {!!}
--}

  sizeassign : ∀ {n x} → (pos 1) ≤ size (compile (x ≔ n)) `ℤ`
  sizeassign {NAT a} = +≤+ (s≤s z≤n)
  sizeassign {VAR s} = +≤+ (s≤s z≤n)
  sizeassign {a + b} = size& -- acomp (a + b) is at least ADD :: [] 

  notSKIP : IExp → Bool
  notSKIP SKIP = false
  notSKIP (a ⋯ b) = notSKIP a ∨ notSKIP b
  notSKIP _    = true

  ns∨ : ∀ {x y} → notSKIP x ≡ false → notSKIP y ≡ false → notSKIP x ∨ notSKIP y ≡ false
  ns∨ {x} {y} p q with notSKIP x | notSKIP y
  ... | false | false = refl
  ns∨ () _ | true | false
  ns∨ _ () | false | true
  ns∨ () () | true | true


  compile>0 : (eprog : IExp){ns : notSKIP eprog ≡ true} → 1 ≤ size`(compile eprog)
  compile>0 SKIP {}
  compile>0 (x ≔ n) with n
  ... | NAT a = s≤s z≤n
  ... | VAR v = s≤s z≤n
  ... | a + b = size`&
  compile>0 (x ⋯ y) {p}  with inspect (notSKIP x) | inspect (notSKIP y)
  ... | true with≡ eqx | b  with≡ eqy rewrite size`&+ {compile x} {compile y} = ≤trans (compile>0 x {eqx}) (≤+ ≤=)
  ... | false with≡ eqx | true  with≡ eqy rewrite size`&+ {compile x} {compile y} | +comm (size` (compile x)) (size` (compile y)) = ≤trans (compile>0 y {eqy}) (≤+ ≤=)
  compile>0 (x ⋯ y) {p} | false with≡ eqx | false with≡ eqy with notSKIP x | notSKIP y
  compile>0 (x ⋯ y) {}  | false with≡ eqx | false with≡ eqy | false | false
  compile>0 (x ⋯ y) {p} | false with≡ ()  | false with≡ eqy | true  | _
  compile>0 (x ⋯ y) {p} | false with≡ eqx | false with≡ ()  | _     | true
  compile>0 (IF b THEN x ELSE y) = ≤trans (s≤s z≤n) (size`&2 {bcomp b false (zuc (size (compile x)))} {compile x} {JMP (size (compile y)) :: []} {compile y})
  compile>0 (WHILE b DO x) = ≤trans (s≤s z≤n) (size`&3 {bcomp b false (size (compile x) z+ pos 1)} {compile x} {JMP (neg (pos (size` (bcomp b false (pos (size` (compile x) ℕ+ 1))) ℕ+ size` (compile x) ℕ+ 1))) :: []})

{--
  verskips : ∀ {eprog state'} → [ ⟦⟧ , eprog ]⇓ state' → notSKIP eprog ≡ false → state' ≡ ⟦⟧
  verskips skip p = refl
  verskips (seqbase) p = verskips a p
  verskips (seqstep a b) p with verskips a (∨fs1 p)
  ... | refl with verskips b (∨fs2 p)
  ... | refl = refl
  verskips assign ()
  verskips (iftrue _) ()
  verskips (iffalse _) ()
  verskips (while _) ()
  verskips while ()
--}

{--
  verskips : ∀ {s} → (eprog : IExp) → notSKIP eprog ≡ false → [ eprog , s ]⇓ s
  verskips SKIP refl = Skip
  verskips (a ⋯ b) p = Seq (verskips a (∨fs1 p)) (verskips b (∨fs2 p))
  verskips (_ ≔ _) ()
  verskips (IF _ THEN _ ELSE _) ()
  verskips (WHILE _ DO _) ()
--}

  t : (eprog : IExp){p : Prog} → compile eprog ≡ p
  t (x ≔ (NAT n)) {LOADI _ :: STORE _ :: []}= {!!}
  

  verify : ∀ {state state' conf' eprog'}(eprog : IExp) → ⟦ state , eprog ⟧↦⟦ state' , eprog' ⟧ → (compile eprog) × (config state $ (pos 0)) ⇒* conf' → state' ≡ (STATE conf')
  verify SKIP ()
  verify a seqbase none = refl
  verify (a ⋯ b) (seqstep stp) none rewrite verify a stp none = refl
  verify (a ⋯ b) (seqstep stp) (join p q) rewrite verify a stp (join _ _) = refl
  verify a while none = refl
  verify a while (join ×LOADI none) = refl
  verify (x ≔ (NAT n)) assign (join ×LOADI (join ×STORE none)) = {!!}

{--
  -- verifies valid finite programs
  verify : ∀ {conf' state'}(eprog : IExp){ssse : ⟦ ⟦⟧ , eprog ⟧↦⟦ state' , SKIP ⟧}{rsteps :  (compile eprog) ⊢ (config ⟦⟧ $ (pos 0)) ⇒* conf'} → state' ≡ (STATE conf')
  verify i {_} {0r _ _} with inspect (notSKIP i)
  verify i {ss} {0r _ _} | false with≡ p = {!!}
--  verify i {_} {0r _ _} | true with≡ p with compile>0 i {p}
--  verify i {_} {0r _ (+≤+ (_))} | true with≡ p | a
  --}
  -- verifies non-terminating programs
