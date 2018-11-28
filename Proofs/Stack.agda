module Proofs.Stack where

  open import Lang.Stack
  open import Base.DataStructures
  open import Data.Bool
  open import Misc.Base
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Agda.Builtin.Equality
  open import Data.Star


  data _⊢_⇒_ : Prog → Config → Config → Set where
    exec1 : ∀ {p c}{vpc : Lem2 (pc c) p} → (i : Inst){ieq : i ≡ (inst p (pc c) {vpc})}{vh : Lem1 i (height (stack c))} → p ⊢ c ⇒ iexe i c vh

  data _⊢_⇒*_ : Prog → Config → Config → Set where
    refl : ∀ {p c} → (end : (pc c) ℤ≡ size p) → p ⊢ c ⇒* c
    step : ∀ {p c c' c''} → p ⊢ c ⇒ c' → p ⊢ c' ⇒* c'' → p ⊢ c ⇒* c''
  
{--  data _↓_↦_ : Prog → Config → Config → Set where --does it make sense to define bss for this? bss should jump through whole prog? sss wuld do what I've done here?
    LIMM : ∀ {p stt stk pc n}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ LOADI n}  → p ↓ config stt stk pc ↦ config stt (n , stk) (zuc pc)
    LVAR : ∀ {p stt stk pc v}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ LOAD v}   → p ↓ config stt stk pc ↦ config stt ((get-var v stt) , stk) (zuc pc) --}
{--
  data _×_⇒_ : Prog → Config → Config → Set where
    ×NOTHING : ∀ {p state stack pc}{done : pc ≡ size p} → p × config state stack pc ⇒ config state stack pc
    ×LOADI : ∀ {p state stack pc n}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ LOADI n} → p × config state stack pc ⇒ config state (n , stack) (zuc pc)
    ×LOAD : ∀ {p state stack pc v}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ LOAD v} → p × config state stack pc ⇒ config state ((get-var v state) , stack) (zuc pc)
    ×STORE : ∀ {p state n rest pc v}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ STORE v} → p × config state (n , rest) pc ⇒ config (set-var v n state) rest (zuc pc)
    ×ADD : ∀ {p state n1 n2 rest pc}{vpc : Lem2 pc p}{eqi : inst p pc {vpc} ≡ ADD} → p × config state (n1 , n2 , rest) pc ⇒ config state ((n1 + n2) , rest) (zuc pc)


--}




























-------------
{--
  data ExeStep (p : Prog)(c : Config)(c' : Config) : Set where
    step : {i : Inst}{l1 : Lem1 i (height (stack c))}{l2 : Lem2 (pc c) p}{defi : i ≡ inst p (pc c) {l2}}{defc' : c' ≡ iexe i c l1 } → ExeStep p c c'

  data Step {A : Set}(r : A → A)(x : A) : A → Set where
    stp : Step r x (r x)
  
  data Star {A : Set}(r : A → A) : A → A → Set where
    none : {x : A} → Star r x x
    some : {x y z : A} → Step r x y → Star r y z → Star r x z

  
  data ⦅_,_⦆↦_ : Prog → Config → Config → Set where
    base : ∀ {p c}{ivpc : (size p) ≤ (pc c) `ℤ`} → ⦅ p , c ⦆↦ c
    trans : ∀ {p c c' c''} → ExeStep p c c' → ⦅ p , c' ⦆↦ c'' → ⦅ p , c ⦆↦ c''

--}
