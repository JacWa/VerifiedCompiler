module Trace where
  open import Base.DataStructures
  open import Misc.Base
  open import Lang.Expr
  open import Lang.Stack
  open import Agda.Builtin.String
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Int renaming (Int to ℤ)
  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Data.List
  open import Data.Maybe

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
  
  traceᴴᴸ : (fuel : ℕ) → IExp → List Bhvr → List Bhvr
  traceᴴᴸ 0 _ t = t
  traceᴴᴸ (suc n) SKIP t = t
  traceᴴᴸ (suc n) (x ≔ a) t = (WRT x (EVA a t) ∷ []) ++ traceA a t
  traceᴴᴸ (suc n) (P ⋯ Q) t = traceᴴᴸ n Q (traceᴴᴸ n P t)
  traceᴴᴸ (suc n) (IF b THEN P ELSE Q) t with EVB b t
  ... | true  = traceᴴᴸ n P (traceB b t)
  ... | false = traceᴴᴸ n P (traceB b t)
  traceᴴᴸ (suc n) (WHILE b DO c) t with EVB b t
  ... | true  = traceᴴᴸ n c (traceB b t)
  ... | false = traceB b t


  traceI : Inst → (Stack × List Bhvr) × ℤ → (Stack × List Bhvr) × ℤ
  traceI (LOADI x)   ((s , t) , pc) = ((x , s) , t) , (pc z+ pos 1)
  traceI (LOAD  v)   ((s , t) , pc) with LV v t
  ... | x = ((x , s) , (RD v x ∷ t)) , (pc z+ pos 1)
  traceI ADD         (((head , next , rest) , t) , pc) = (((head ℕ+ next) , rest) , t) , (pc z+ pos 1)
  traceI (STORE x)   (((head , rest) , t) , pc)        = (rest , (WRT x head ∷ t)) , (pc z+ pos 1)
  traceI (JMP x)     (s,t , pc) = s,t , ( pc z+ x z+ pos 1)
  --traceI (JMPLESS x) 
  --traceI (JMPGE x)
{- may need a more sophisticated way to deal with these cases, rather than just doing nothing
   these should never occur, due to the way programs are compiled.
   ↑ maybe I need a proof for that? ↑
   or maybe just ignore the instruction and increment the program counter?-}
  traceI ADD t = t
  traceI (STORE _) t = t
  traceI (JMPLESS _) t = t
  traceI (JMPGE _) t = t
  

  traceᴸᴸ' : (fuel : ℕ) → Prog → (PC : ℤ) → Stack × List Bhvr → Stack × List Bhvr
  traceᴸᴸ' 0 _ _ s,t = s,t
  traceᴸᴸ' (suc n) P PC s,t with iz (size P) ≤ PC
  ... | true = s,t
  ... | false with P ፦ PC
  ... | nothing = s,t -- maybe create proof with iz so that this case is not possible
  ... | just i with traceI i (s,t , PC)
  ... | s,t' , PC' = traceᴸᴸ' n P PC' (s,t')
  

  traceᴸᴸ :  (fuel : ℕ) → Prog → List Bhvr
  traceᴸᴸ n p = snd (traceᴸᴸ' n p (pos 0) ($ , []))
