module Proofs.Compiler where

  open import Compiler
  open import Lang.Stack
  open import Lang.Expr
  open import Proofs.Basic
  open import Proofs.Stack
  open import Proofs.Expr
  open import Proofs.NatProofs
  open import Misc.Base
  open import Base.DataStructures
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _ℕ+_)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_) hiding (_≟_)
  open import Data.Bool.Base
  open import Relation.Nullary

  compexec : ∀ {p q σ σ' σ'' s s' s'' pc' pc''} → p ⊢ (config σ s (pos 0)) ⇒* (config σ' s' pc') → size p ≡ pc' → q ⊢ (config σ' s' (pos 0)) ⇒* (config σ'' s'' pc'') → (p & q) ⊢ (config σ s (pos 0)) ⇒* (config σ'' s'' ((size p) z+ pc''))
  compexec = {!!}

  _∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
  (f ∘ g) x = g (f x) 


  asound :  ∀ a {σ s}  → acomp a ⊢ config σ s (pos 0) ⇒* config σ ((aexe a σ) , s) (size (acomp a))
  asound (NAT n) = step (exec1 (LOADI n) refl {loadi}) 0r
  asound (VAR x) = step (exec1 (LOAD x) refl {load}) 0r
  asound (m + n) rewrite size`&3= (acomp m) (acomp n) (ADD :: []) = compexec (asound m) refl (compexec (asound n) refl (step  (exec1 ADD refl {add}) (0r)))


{-Δpc : BExp → Bool → ℤ → ℤ
  Δpc (BOOL b) f offset with b ≟ f
  ... | yes refl = offset z+ (pos 1)
  ... | no _     = pos 0
  Δpc (NOT b) f offset = Δpc b (not f) offset
  Δpc (a AND b) f offset = {!!}-}

  Δpc : BExp → State → Bool → ℤ → ℤ
{-  Δpc (BOOL b) _ f offset with b ≟ f
  ... | yes refl = offset z+ (pos 1)
  ... | no _     = pos 0
  Δpc (NOT b) σ f offset = Δpc b σ (not f) offset
  Δpc (a AND b) σ f offset with f
  ... | true = {!!}
  ... | false = {!!}
-}
  Δpc bexp σ flag offset with flag | bexe bexp σ
  ... | true | true = offset z+ size (bcomp bexp flag offset)
  ... | false | false = offset z+ size (bcomp bexp flag offset)
  ... | true | false = size (bcomp bexp flag offset)  
  ... | false | true = size (bcomp bexp flag offset)

  bsound : ∀ b flag offset {σ s} → (bcomp b flag offset) ⊢ config σ s (pos 0) ⇒* config σ s (Δpc b σ flag offset)
  bsound (BOOL true) true offset = step {JMP offset :: []} (exec1 (JMP offset) refl {jmp}) 0r
  bsound (BOOL false) false offset = step {JMP offset :: []} (exec1 (JMP offset) refl {jmp}) 0r
  bsound (BOOL true) false offset = 0r
  bsound (BOOL false) true offset = 0r
  bsound (NOT (BOOL b)) flag offset with b | flag
  ... | true | true = 0r
  ... | false | false = 0r
  ... | true | false = step {JMP offset :: []} (exec1 (JMP offset) refl {jmp}) 0r
  ... | false | true = step {JMP offset :: []} (exec1 (JMP offset) refl {jmp}) 0r



  sound : ∀ E {σ σ' s} → [ E , σ ]⇓ σ' → compile E ⊢ config σ s (pos 0) ⇒* config σ' s (size (compile E))
  sound SKIP Skip = 0r
  sound (x ≔ a) Assign rewrite size`&= (acomp a) (STORE x :: []) = compexec (asound a) refl (step (exec1 (STORE x ) refl {store}) (0r))
  sound (P ⋯ Q) (Seq p q) rewrite size`&= (compile P) (compile Q) = compexec (sound P p) refl (sound Q q)
{-sound (IF b THEN P ELSE Q) S with S
  ... | IfFalse e q = {!!}
  ... | IfTrue e p = {!!}-}
  sound (WHILE b DO C) S with S
  ... | WhileFalse e = compexec {!!} {!!} {!!}
  ... | WhileTrue e c w = {!!}








{-
  Fₐ : AExp → ℤ
  Fₐ = acomp ∘ size

  F : IExp → ℤ
  F SKIP  = pos 0
  F (x ≔ n) = pos 1 z+ (Fₐ n)
  F (SKIP ⋯ E) = pos 0
  F (E ⋯ E') = F E
  F (IF _ THEN _ ELSE _) = pos 0
  F (WHILE _ DO _) = pos 0

  sssound : ∀ E {E' σ σ' s} → ⟦ σ , E ⟧↦⟦ σ' , E' ⟧ → compile E ⊢ config σ s (pos 0) ⇒* config σ' s (F E)
  sssound SKIP ()
  sssound (x ≔ a) assign rewrite suc≡+1 (size` (acomp a)) | zucpn-pn≡1 (size` (acomp a)) = compexec (asound a) refl (step (exec1 (STORE x ) refl {store}) (0r))
  sssound (SKIP ⋯ P) seqbase = 0r
  sssound (P ⋯ Q) (seqstep p) = {!!}
  sssound (IF b THEN x ELSE y) (iftrue p) = 0r
  sssound (IF b THEN x ELSE y) (iffalse p) = 0r
  sssound (WHILE b DO c) while = 0r
-}
  

  {--

  asound :  ∀ a {σ n s} → [ a , σ ]⇃ n → acomp a × config σ s (pos 0) ⇒* config σ (n , s) (size (acomp a))
  asound (NAT n) Nat = some (×LOADI refl) (none refl)
  asound (VAR x) Vrr = some (×LOAD refl) (none refl)
  asound (m + n) (Pls aₘ aₙ) = {!!}
 --}

{-
  asound : ∀ a {σ s} → acomp a × config σ s (pos 0) ⇒* config σ (aexe a σ , s) (size (acomp a))
  asound (NAT n) = some (×LOADI refl) none
  asound (VAR x) = some (×LOAD refl) none
  asound (m + n) = {!!}

  sound : ∀ E {E' σ σ' s} → ⟦ σ , E ⟧↦⟦ σ' , E' ⟧ → compile E × config σ s (pos 0) ⇒* config σ' s (F E)
  sound SKIP ()
  sound (x ≔ a) assign with a
  ... | NAT n = {!!} --some (×LOADI refl) (some (×STORE refl) none)
  ... | VAR s = some (×LOAD refl) (some (×STORE refl) none)
  ... | m + n = {!!}
  sound (SKIP ⋯ E) seqbase = none
  sound (E ⋯ E') (seqstep {SKIP} ())
  sound (E ⋯ E') (seqstep p) = {!!}
  sound (IF b THEN x ELSE y) (iftrue p) = none
  sound (IF b THEN x ELSE y) (iffalse p) = none
  sound (WHILE b DO c) while = none

-}
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
