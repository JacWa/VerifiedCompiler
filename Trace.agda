module Trace where
  open import Base.DataStructures
  open import Misc.Base
  open import Lang.Expr 
  open import Lang.Stack renaming (JMPLESS to JMPLT)
  open import Agda.Builtin.String
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Data.List
  open import Data.Maybe
  open import Compiler

  data Bhvr : Set where
    RD : String → ℕ → Bhvr
    WRT : String → ℕ → Bhvr

--The convention for the order of memory traces I use is reverse order.
--It makes it easier to code the below function LV to find the last stored value of a variable.
  LV : String → List Bhvr → ℕ 
  LV x [] = 0
  LV x ((WRT y n) ∷ xs) with primStringEquality x y
  ... | true = n
  ... | false = LV x xs
  LV x (_ ∷ xs) = LV x xs 


  EVA : AExp → List Bhvr → ℕ
  EVA (NAT n) t = n
  EVA (VAR x) [] = 0
  EVA (VAR x) ((RD _ _) ∷ ts) = EVA (VAR x) ts
  EVA (VAR x) ((WRT y n) ∷ ts) with primStringEquality x y
  ... | true = n
  ... | false = EVA (VAR x) ts
  EVA (x + y) t = EVA x t ℕ+ EVA y t

  EVB : BExp → List Bhvr → Bool
  EVB (BOOL b) _ = b
  EVB (NOT b) t  = ! (EVB b t)
  EVB (a AND b) t with EVB a t | EVB b t
  ... | true | true = true
  ... | _ | _ = false
  EVB (x LT y) t = ! (is (EVA y t) ≤ (EVA x t))

  traceA : AExp → List Bhvr → List Bhvr
  traceA (NAT _) t = t
  traceA (VAR x) t = RD x (LV x t) ∷ [] ++ t
  traceA (a + b) t = traceA b (traceA a t)  --after compilation, a will be executed first.

  traceB : BExp → List Bhvr → List Bhvr
  traceB (BOOL _)  t = t
  traceB (NOT b)   t = traceB b t
  traceB (x AND y) t = traceB y (traceB x t)
  traceB (x LT y)  t = traceA y (traceA x t)

  {-# TERMINATING #-}
  traceᴴᴸ' :  IExp → List Bhvr × ℕ → List Bhvr × ℕ
  traceᴴᴸ' _ (t , 0) = (t , 0)
  traceᴴᴸ' SKIP (t , (suc n)) = t , n
  traceᴴᴸ' (x ≔ a) (t , (suc n)) = ((WRT x (EVA a t) ∷ []) ++ traceA a t) , n
  traceᴴᴸ' (P ⋯ Q) (t , suc n) = traceᴴᴸ' Q (traceᴴᴸ' P (t , n))
  traceᴴᴸ' (IF b THEN P ELSE Q) (t , suc n) with EVB b t
  ... | true  = traceᴴᴸ' P ((traceB b t) , n)
  ... | false = traceᴴᴸ' Q ((traceB b t) , n)
  traceᴴᴸ' (WHILE b DO c) (t , suc n) with EVB b t
  ... | true  = traceᴴᴸ' (c ⋯ (WHILE b DO c)) ((traceB b t) , n)
  ... | false = traceB b t , n


  traceᴴᴸ : (fuel : ℕ) → IExp → List Bhvr
  traceᴴᴸ n P = fst (traceᴴᴸ' P ([] , n))

{-
  traceI : Inst → (Stack × List Bhvr) × ℤ → (Stack × List Bhvr) × ℤ
  traceI (LOADI x)   ((s , t) , pc) = ((x , s) , t) , (pc z+ pos 1)
  traceI (LOAD  v)   ((s , t) , pc) with LV v t
  ... | x = ((x , s) , (RD v x ∷ t)) , (pc z+ pos 1)
  traceI ADD         (((head , next , rest) , t) , pc) = (((head ℕ+ next) , rest) , t) , (pc z+ pos 1)
  traceI (STORE x)   (((head , rest) , t) , pc)        = (rest , (WRT x head ∷ t)) , (pc z+ pos 1)
  traceI (JMP x)     (s,t , pc) = s,t , ( pc z+ x z+ pos 1)
  traceI (JMPLESS x) (((head , next , rest) , t) , pc) with is head ≤ next
  ... | true  = (rest , t) , (pc z+ pos 1)
  ... | false = (rest , t) , (pc z+ x z+ pos 1) 
  traceI (JMPGE x) (((head , next , rest) , t) , pc) with is head ≤ next
  ... | true  = (rest , t) , (pc z+ x z+ pos 1)
  ... | false = (rest , t) , (pc z+ pos 1)
{- may need a more sophisticated way to deal with these cases, rather than just doing nothing
   these should never occur, due to the way programs are compiled.
   ↑ maybe I need a proof for that? ↑
   or maybe just ignore the instruction and increment the program counter?-}
  traceI ADD t = t
  traceI (STORE _) t = t
  traceI (JMPLESS _) t = t
  traceI (JMPGE _) t = t
 -}
  

  traceᴸᴸ' : (fuel : ℕ) → Prog → (PC : ℤ) → Stack × List Bhvr → Stack × List Bhvr
  traceᴸᴸ' 0 _ _ s,t = s,t
  traceᴸᴸ' (suc n) P PC s,t with P ፦ PC
  ... | nothing = s,t
  traceᴸᴸ' (suc n) P PC (s , t) | just i with i
  ... | LOADI x = traceᴸᴸ' n P (zuc PC) ((x , s) , t)
  ... | LOAD v with LV v t
  ... | x = traceᴸᴸ' n P (zuc PC) ((x , s) , (RD v x ∷ t))
  traceᴸᴸ' (suc n) P PC (s , t) | just i | ADD = traceᴸᴸ' n P (zuc PC) (((hd s ℕ+ hd (tl s)) , tl (tl s)) , t)
  traceᴸᴸ' (suc n) P PC (s , t) | just i | STORE v = traceᴸᴸ' n P (zuc PC) (tl s , (WRT v (hd s) ∷ t))
  traceᴸᴸ' (suc n) P PC s,t | just i | JMP x = traceᴸᴸ' n P (zuc PC z+ x) s,t
  traceᴸᴸ' (suc n) P PC (s , t) | just i | JMPLT x with is hd s ≤ hd (tl s)
  ... | true = traceᴸᴸ' n P (zuc PC) (s , t)
  ... | false = traceᴸᴸ' n P (zuc PC z+ x) (s , t)
  traceᴸᴸ' (suc n) P PC (s , t) | just i | JMPGE x with is hd s ≤ hd (tl s)
  ... | true = traceᴸᴸ' n P (zuc PC z+ x) (s , t)
  ... | false = traceᴸᴸ' n P (zuc PC) (s , t)
  
{-traceI i (s,t , PC)
  ... | s,t' , PC' with iz PC' ≤ PC
  ... | true = traceᴸᴸ' n P PC' (s,t')
  ... | false = traceᴸᴸ' (suc n) P PC' (s,t')
-}
  traceᴸᴸ :  (fuel : ℕ) → Prog → List Bhvr
  traceᴸᴸ n p = snd (traceᴸᴸ' n p (pos 0) ($ , []))


  fuelᴴᴸ²ᴸᴸ' : IExp → ℕ × List Bhvr → ℕ × List Bhvr
  fuelᴴᴸ²ᴸᴸ' SKIP f,b = f,b
  fuelᴴᴸ²ᴸᴸ' (x ≔ a) (fuel , b) = (fuel ℕ+ (size` (acomp a))) , b
  fuelᴴᴸ²ᴸᴸ' (x ⋯ x₁) f,b = fuelᴴᴸ²ᴸᴸ' x₁ (fuelᴴᴸ²ᴸᴸ' x f,b)
  fuelᴴᴸ²ᴸᴸ' (IF bl THEN x ELSE y) (fuel , b) with EVB bl b
  ... | true  = fuelᴴᴸ²ᴸᴸ' x ((fuel ℕ+ size` (bcomp bl false (size (compile x) z+ (pos 1)))) , b)
  ... | false = fuelᴴᴸ²ᴸᴸ' y ((fuel ℕ+ size` (bcomp bl false (size (compile x) z+ (pos 1)))) , b)
  fuelᴴᴸ²ᴸᴸ' (WHILE bl DO c) (fuel , b) with EVB bl b
  ... | true = fuelᴴᴸ²ᴸᴸ' c ((fuel ℕ+ 1 ℕ+ size` (bcomp bl false (size (compile c) z+ pos 1))) , b)
  ... | false = (fuel ℕ+ size` (bcomp bl false (size (compile c) z+ pos 1))) , b

  {-# TERMINATING #-}
  fᴴᴸ2ᴸᴸ' : IExp → ℕ × ℕ × State → ℕ × ℕ × State
  fᴴᴸ2ᴸᴸ' _        (0 , fᴸᴸ , σ)         = (0 , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' SKIP     (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , fᴸᴸ , σ)
  fᴴᴸ2ᴸᴸ' (x ≔ a) (suc fᴴᴸ , fᴸᴸ , σ) = (fᴴᴸ , suc (fᴸᴸ ℕ+ size` (acomp a)) , ((x ≔ (aexe a σ)) ∷ σ))
  fᴴᴸ2ᴸᴸ' (P ⋯ Q) (suc fᴴᴸ , fᴸᴸ , σ) = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ2ᴸᴸ' P (suc fᴴᴸ , fᴸᴸ , σ))
  fᴴᴸ2ᴸᴸ' (IF b THEN P ELSE Q) ((suc fᴴᴸ) , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' P (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (pos 1)))) , σ)
  ... | false = fᴴᴸ2ᴸᴸ' Q (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile P) z+ (pos 1)))) , σ)
  fᴴᴸ2ᴸᴸ' (WHILE b DO c) (suc fᴴᴸ , fᴸᴸ , σ) with bexe b σ
  ... | true  = fᴴᴸ2ᴸᴸ' (c ⋯ (WHILE b DO c)) (fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ pos 1))) , σ)
  ... | false = fᴴᴸ , (fᴸᴸ ℕ+ size` (bcomp b false (size (compile c) z+ pos 1))) , σ

  fᴴᴸ2ᴸᴸ : IExp → ℕ → ℕ
  fᴴᴸ2ᴸᴸ I fᴴᴸ with fᴴᴸ2ᴸᴸ' I (fᴴᴸ , 0 , ⟦⟧)
  ... | fᴴᴸ' , fᴸᴸ , _ = fᴴᴸ' ℕ+ fᴸᴸ

