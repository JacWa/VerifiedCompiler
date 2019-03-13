module Proofs.Trace where

  open import Relation.Binary
  open import Relation.Binary.Core
  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Relation.Nullary
  open import Function

  open import Agda.Builtin.Int
  
  open import Data.Empty
  open import Data.Bool
  open import Data.String
  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Data.List
  open import Data.Maybe

  open import Proofs.NatProofs

  open import Base.DataStructures
  open import Misc.Base
  open import Lang.Expr
  open import Lang.Stack
  open import Compiler
  open import Trace




  ---------------------------------------------------------------------------
  --- Proof of equality for traces over arithmetic expression compilation ---
  ---------------------------------------------------------------------------
  
  ---------------------------------------------------------------------------
  --- Proof of equality for traces over boolean expression compilation ---
  ---------------------------------------------------------------------------

  btransEQ : ∀ b f {offset} → traceB b [] ≡ snd (traceᴸᴸ' f (bcomp b false offset) (pos 0) ($ , []))
  btransEQ (BOOL b) 0 = refl
  btransEQ (BOOL true) (suc n) = refl
  btransEQ (BOOL false) (suc n) = {!!}
  
 -- btransEQ (BOOL b) t f o with false Data.Bool.≟ b
 -- ... | yes p = {!!}
 -- ... | no _  with traceᴸᴸ' f [] (pos 0) ($ , t)
 -- ... | w = {!!}
  
  -------------------------------------------------------------------
  --- Proof of equality for traces over whole program compilation ---
  -------------------------------------------------------------------

  transEQ-helper-1a : ∀ i → is size` (i :: []) ≤ 0 ≡ false
  transEQ-helper-1a = λ i → refl

  transEQ-helper-1b : ∀ x n → is x ≤ n ≡ false → is (suc x) ≤ n ≡ false
  transEQ-helper-1b 0 n ()
  transEQ-helper-1b (suc y) 0 prf = refl
  transEQ-helper-1b (suc y) (suc n) prf = transEQ-helper-1b y n prf

  transEQ-helper-1c : ∀ x y n → is y ≤ n ≡ false → is (x ℕ+ y) ≤ n ≡ false
  transEQ-helper-1c 0       y _ prf rewrite +comm 0       y = prf
  transEQ-helper-1c (suc x) y n prf = transEQ-helper-1b (x ℕ+ y) n (transEQ-helper-1c x y n prf)

  transEQ-helper-1 : ∀ P {P'} → is size` P' ≤ 0 ≡ false → is size` (P & P') ≤ 0 ≡ false
  transEQ-helper-1 P {P'} prf rewrite size`&+ {P} {P'} = transEQ-helper-1c (size` P) (size` P') 0 prf

  transEQ-helper-2 : ∀ b f c  → EVB b [] ≡ false → traceᴸᴸ f (compile (WHILE b DO c)) ≡ traceᴸᴸ f (bcomp b false (pos (size` (compile c) ℕ+ 1)))
  transEQ-helper-2 = {!!}

  transEQ-helper-3 : ∀ b c f → is size` (bcomp b false (pos (size` (compile c) ℕ+ 1))) ≤ 0 ≡ true → traceᴴᴸ f (WHILE b DO c) ≡ []
  transEQ-helper-3 = {!!}

--  transEQ-helper-whiletrue-a : ∀ I P Q t f f' f'' → t ≡ snd (traceᴸᴸ' f' P (pos 0) ($ , [])) → traceᴴᴸ' f I [] ≡ snd (traceᴸᴸ' f'' (P & Q) (size P) ($ , [])) → traceᴴᴸ' f I t ≡ snd (traceᴸᴸ' f' (P & Q) (pos 0) ($ , []))
--  transEQ-helper-whiletrue-a = {!!}


 -- transEQ-helper-whiletrue-b : ∀ f b c → traceᴴᴸ' (suc f) (c ⋯ (WHILE b DO c)) [] ≡ snd (traceᴸᴸ' (suc f) (compile (WHILE b DO c)) (size (bcomp b false (pos (size` (compile c) ℕ+ 1)))) ($ , []))
 -- transEQ-helper-whiletrue-b = {!!}


  helper-a : ∀ P Q fuel s,t →  traceᴸᴸ' fuel (P & Q) (pos 0) (s,t) ≡ traceᴸᴸ' fuel (P & Q) (size P) (traceᴸᴸ' fuel P (pos 0) (s,t))
  helper-a _ _ 0 _  = refl
  helper-a [] _ (suc f) _  = refl
  helper-a (p :: ps) Q (suc f) s,t with traceᴸᴸ' (suc f) (p :: ps) (pos 0) s,t
  ... | s , t = {!!}

{--  transEQ-helper-whiletrue : ∀ {f b c} → traceᴴᴸ' f (c ⋯ (WHILE b DO c)) (traceB b []) ≡ snd (traceᴸᴸ' (suc f) (compile (WHILE b DO c)) (pos 0) ($ , []))
  transEQ-helper-whiletrue {suc f} {b} {c} =
    transEQ-helper-whiletrue-a
    (c ⋯ (WHILE b DO c))
    (bcomp b false (pos (size` (compile c) ℕ+ 1)))
    (compile c & JMP (neg (pos (size` (bcomp b false (pos (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])
    (traceB b [])
    (suc f)
    (suc (suc f))
    (suc f)
    {!!} --(btransEQ b [] (suc (suc f)) (pos (size` (compile c) ℕ+ 1)))
    (transEQ-helper-whiletrue-b f b c)
--}

  whiletrue-helper-1 : ∀ f b c → fst (traceᴴᴸ' (WHILE b DO c) ([] , suc f)) ≡ snd (traceᴸᴸ' (suc f) (compile (WHILE b DO c)) (pos 0) ($ , []))
  whiletrue-helper-1 = ?

  transEQ : ∀ P {f} → traceᴴᴸ f P ≡ traceᴸᴸ f (compile P)
  transEQ _ {0} = {!!} --refl
  transEQ SKIP {suc f} = refl
  --transEQ (x ≔ a) {suc f} with EVA a [] | traceA a []
  --... | n | t rewrite transEQ-helper-1 (acomp a) {STORE x :: []} refl = {!!}
  transEQ (WHILE b DO c) {suc f} with inspect (EVB b [])
  ... | false with≡ prf rewrite transEQ-helper-2 b (suc f) c prf with inspect (is size` (bcomp b false (pos (size` (compile c) ℕ+ 1))) ≤ 0)
  ... | true with≡ prf2 rewrite transEQ-helper-3 b c (suc f) prf2 | prf2 = refl
  ... | false with≡ prf2 rewrite prf = btransEQ b (suc f)
 -- ... | true  = {!!}
  transEQ (WHILE b DO c) {suc f} | true with≡ prf = {!!}






{-
{-  _≈_ : Decidable {A = Bhvr} _≡_
  RD x y ≈ RD a b with x ≟' a | y ≟'' b
  ... | yes p | yes q rewrite p | q = yes refl
  ... | _ | no q = no (λ t → q {!!})
  RD _ _ ≈ WRT _ _ = no (λ ())
  WRT _ _ ≈ RD _ _ = no (λ ())
-}

  _`≟_ : Bhvr → Bhvr → Bool
  RD _ _ `≟ WRT _ _ = false
  WRT _ _ `≟ RD _ _ = false
  
  eq-helper1 : {x : Bhvr}(xs ys : List Bhvr) → xs ≡ ys → x ∷ xs ≡ x ∷ ys
  eq-helper1 [] [] _ = refl
  eq-helper1 (x ∷ xs) (y ∷ ys) p rewrite p = refl
  eq-helper1 [] (y ∷ ys) ()
  eq-helper1 (x ∷ xs) [] ()

  eq-helper2 : (x y : Bhvr){xs : List Bhvr} → x ∷ xs ≡ y ∷ xs → x ≡ y
  eq-helper2 x y refl = refl
  {-
  eq-help : {x y : Bhvr}{xs ys : List Bhvr} → Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
  eq-help (yes p) (yes q) rewrite p | q = yes refl
  eq-help (no p)  _ = no {!!}

  _≟_ : Decidable {A = List Bhvr} _≡_
  [] ≟ [] = yes refl
  (x ∷ xs) ≟ (y ∷ ys) = eq-help (x  y) (xs ≟ ys)
  (_ ∷ _) ≟ [] = no λ ()
  [] ≟ (_ ∷ _) = no λ ()
  

-}-}
