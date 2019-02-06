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

  _∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
  (f ∘ g) x = g (f x) 

  Fₐ : AExp → ℤ
  Fₐ = acomp ∘ size

  F : IExp → ℤ
  F SKIP  = pos 0
  F (x ≔ n) = pos 1 z+ (Fₐ n)
  F (SKIP ⋯ E) = pos 0
  F (E ⋯ E') = F E
  F (IF _ THEN _ ELSE _) = pos 0
  F (WHILE _ DO _) = pos 0

  {--

  asound :  ∀ a {σ n s} → [ a , σ ]⇃ n → acomp a × config σ s (pos 0) ⇒* config σ (n , s) (size (acomp a))
  asound (NAT n) Nat = some (×LOADI refl) (none refl)
  asound (VAR x) Vrr = some (×LOAD refl) (none refl)
  asound (m + n) (Pls aₘ aₙ) = {!!}
 --}


  asound : ∀ a {σ s} → acomp a × config σ s (pos 0) ⇒* config σ (aexe a σ , s) (size (acomp a))
  asound (NAT n) = some (×LOADI refl) (none refl)
  asound (VAR x) = some (×LOAD refl) (none refl)
  asound (m + n) = {!!}

  sound : ∀ E {E' σ σ' s} → ⟦ σ , E ⟧↦⟦ σ' , E' ⟧ → compile E × config σ s (pos 0) ⇒* config σ' s (F E)
  sound SKIP ()
  sound (x ≔ a) assign with a
  ... | NAT n = some (×LOADI refl) (some (×STORE refl) (none refl))
  ... | VAR s = some (×LOAD refl) (some (×STORE refl) (none refl))
  ... | m + n = {!!}
  sound (SKIP ⋯ E) seqbase = none refl
  sound (E ⋯ E') (seqstep {SKIP} ())
  sound (E ⋯ E') (seqstep p) = {!!}
  sound (IF b THEN x ELSE y) (iftrue p) = none refl
  sound (IF b THEN x ELSE y) (iffalse p) = none refl
  sound (WHILE b DO c) while = none refl 


{--
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

  

  &right : ∀ P Q {C C'} → P × C ⇒* C' → (P & Q) × C ⇒* C' 
  &right = {!!}

  rw : ∀ P Q → compile (P ⋯ Q) ≡ compile P & compile Q
  rw P Q = {!!}

  feskip : IExp → Bool
  feskip SKIP = true
  feskip (SKIP ⋯ E) = true
  feskip _ = false
  
  ns⇒dn : ∀ E E' {C C'} → notSKIP E ≡ false → compile E' × C ⇒* C' → compile (E ⋯ E') × C ⇒* C'
  ns⇒dn = {!!}
  

  verify : ∀ {σ σ' E' pc' stk}(E : IExp)(lb : (pos 0) ≤ (pos 0) `ℤ`)(ub : (pos 0)  < (size (compile E)) `ℤ`) →
           --------------------------------------------------------------------------------------------------
                  ⟦ σ , E ⟧↦⟦ σ' , E' ⟧ → (compile E) × (config σ stk (pos 0)) ⇒* (config σ' stk pc')
  verify SKIP _ _ ()
  verify (x ≔ n) lb ub assign with n   ---------------- I HAVE TO ASSUME pc' ≡ 2!!!!
  ... | NAT m = some (×LOADI {n = m} lb ub {refl}) (some (×STORE (+≤+ z≤n) (+≤+ (s≤s (s≤s z≤n))) {refl}) (none {!!}))
  ... | VAR y = {!!}
  ... | a + b = {!!}
  verify (E ⋯ E') lb ub seqbase = none {!!}
  verify (E ⋯ E') lb ub (seqstep s) with inspect (notSKIP E)
  ... | true with≡ p = &right (compile E) (compile E') (verify E lb (+≤+ (compile>0 E {p})) s)
  verify {σ} {σ'} {E''} {pc'} {stk} (E ⋯ E') lb ub (seqstep s) | false with≡ p = ns⇒dn E E' p (verify E' lb {!!} {!!})

  bssound : ∀ E {σ σ' stk} → [ E , σ ]⇓ σ' → (compile E) × (config σ stk (pos 0)) ⇒* (config σ' stk (size (compile E)))
  bssound SKIP Skip = none refl
  bssound (x ≔ n) Assign with n
  ... | NAT i = {!!}
{--
  verify (E ⋯ E') lb ub _ with inspect (notSKIP E)
  verify _ _ _ seqbase | false with≡ p = none {!!}
  verify (E ⋯ E') lb ub (seqstep s) | true with≡ p = &right (compile E) (compile E') (verify E lb (+≤+ (compile>0 E {p})) s)
  verify _ _ _ seqbase | true with≡ ()
  verify (E ⋯ E') lb ub (seqstep s) | false with≡ p with feskip E
  verify (E ⋯ E') lb ub (seqstep s) | false with≡ p | true = {!!}
  verify (E ⋯ E') lb ub (seqstep s) | false with≡ () | false --}
  {--
  verify _ _ _ seqbase | SKIP = none {!!}
  verify (E ⋯ E') lb ub (seqstep s) | (e) = &right (compile (e)) (compile E') (verify (e) lb (+≤+ (compile>0 (e) {refl})) s)
--}
  

{--
  verify : ∀ {state state' conf' eprog' stack pc}(eprog : IExp) → ⟦ state , eprog ⟧↦⟦ state' , eprog' ⟧ → (compile eprog) × (config state stack (pc)) ⇒* conf' → state' ≡ (STATE conf')
  verify SKIP ()
  verify a seqbase none = refl
  verify (a ⋯ b) (seqstep stp) none rewrite verify a stp none = refl
  -- verify (a ⋯ b) (seqstep stp) (some p q) rewrite verify a stp (some _ _) = refl
  verify a while none = refl
  -- verify a while (some ×LOADI none) = refl
  -- verify (x ≔ (NAT n)) assign (some ×LOADI (some ×STORE none)) = {!!}
--}
{--
  -- verifies valid finite programs
  verify : ∀ {conf' state'}(eprog : IExp){ssse : ⟦ ⟦⟧ , eprog ⟧↦⟦ state' , SKIP ⟧}{rsteps :  (compile eprog) ⊢ (config ⟦⟧ $ (pos 0)) ⇒* conf'} → state' ≡ (STATE conf')
  verify i {_} {0r _ _} with inspect (notSKIP i)
  verify i {ss} {0r _ _} | false with≡ p = {!!}
--  verify i {_} {0r _ _} | true with≡ p with compile>0 i {p}
--  verify i {_} {0r _ (+≤+ (_))} | true with≡ p | a
  --}
  -- verifies non-terminating programs
--}
