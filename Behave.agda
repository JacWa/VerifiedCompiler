module Behave where

  open import Lang.Stack
  open import Lang.Expr
  open import Data.Nat.Base renaming (_+_ to _ℕ+_)
  open import Data.String.Base using (String; primStringEquality)
  open import Base.DataStructures
  open import Agda.Builtin.Bool
  open import Data.Colist renaming (_∷_ to _ph_)
  open import Coinduction
  open import Relation.Binary


  data _×_ (A : Set)(B : Set) : Set where   --- Pair type
    _,_ : (a : A) → (b : B) →  A × B

  _[0] : ∀ {A B} → A × B → A
  (a , _) [0] = a

  _[1] : ∀ {A B} → A × B → B
  (_ , b) [1] = b

  data Bhvr : Set where
    RD : String → ℕ → Bhvr
    WRT : String → ℕ → Bhvr

  data List (A : Set) : Set where
    [] : List A
    _::_ : (a : A) → List A → List A
{--
  ex : Colist Bhvr × State → State
  ex ([] , s) = s
  ex ((x ph xs) , s) with x
  ... | RD _ = ex (♭ xs , s)
--}

  data ∞? (A : Set) : Set where
    fin : List A → ∞? A
    inf : Colist A → ∞? A
  

  LW : String → List Bhvr → ℕ
  LW x [] = 0
  LW x ((WRT y n) :: xs) with primStringEquality x y
  ... | true = n
  ... | false = LW x xs
  LW x (b :: xs) = LW x xs

  EVA : AExp → List Bhvr → ℕ
  EVA (NAT n) t = n
  EVA (VAR x) [] = 0
  EVA (VAR x) ((RD _ _) :: ts) = EVA (VAR x) ts
  EVA (VAR x) ((WRT y n) :: ts) with primStringEquality x y
  ... | true = n
  ... | false = EVA (VAR x) ts
  EVA (x + y) t = EVA x t ℕ+ EVA y t

  EVB : BExp → List Bhvr → Bool
  EVB = λ _ _ → false
{--
  tl : {A : Set} → Colist A → Colist A
  tl [] = []
  tl (x ph xs) = ♭ xs
--}

  infixr 21 _⊹⊹_ 
  _⊹⊹_ : ∀ {A} → List A → List A → List A
  []        ⊹⊹ Q = Q
  (x :: xs) ⊹⊹ Q = x :: (xs ⊹⊹ Q)

  f2i : ∀ {A} → List A → Colist A
  f2i [] = []
  f2i (x :: xs) = x ph ♯ (f2i xs)

  _⊕_ : ∀ {A : Set} → ∞? A → ∞? A → ∞? A
  (fin x) ⊕ (fin y) = fin (x ⊹⊹ y)
  (inf x) ⊕ (inf y) = inf (x ++ y)
  (inf x) ⊕ (fin y) = inf (x ++ (f2i y))
  (fin x) ⊕ (inf y) = inf ((f2i x) ++ y)
  

  tracesA : AExp → List Bhvr → List Bhvr
  tracesA (NAT _) _ = []
  tracesA (VAR x) t = RD x (LW x t) :: []
  tracesA (a + b) t = tracesA b t ⊹⊹ tracesA a t

  tracesB : BExp → List Bhvr → List Bhvr
  tracesB (BOOL _)  t = []
  tracesB (NOT b)   t = tracesB b t
  tracesB (x AND y) t = tracesB x t ⊹⊹ tracesB y t
  tracesB (a LT b)  t = tracesA b t ⊹⊹ tracesA a t

  traces : IExp → ∞? Bhvr → ∞? Bhvr
  traces _ (inf t) = inf []
  traces SKIP t = t
  traces (x ≔ n) (fin t) = fin (WRT x (EVA n t) :: tracesA n t)
  traces (P ⋯ Q) t with traces P t
  ... | tₚ = traces Q tₚ ⊕ tₚ
  traces (IF b THEN P ELSE Q) (fin t) with EVB b t
  ... | true = traces P (fin t)
  ... | false = traces Q (fin t)
  traces (WHILE b DO c) t = {!!}
  

{--  
  traces* : IExp → Colist Bhvr
  traces* i = traces i ⟦⟧ [0]

--}
  {--

  infixr 21 _⊹⊹_ 
  _⊹⊹_ : ∀ {A} → List A → List A → List A
  []        ⊹⊹ Q = Q
  (x :: xs) ⊹⊹ Q = x :: (xs ⊹⊹ Q)
  
  tracesA : AExp → List Bhvr
  tracesA (NAT _) = []
  tracesA (VAR x) = (RD x) :: []
  tracesA (a + b) = tracesA a ⊹⊹ tracesA b

  tracesB : BExp → List Bhvr
  tracesB (BOOL _)  = []
  tracesB (NOT b)   = tracesB b
  tracesB (x AND y) = tracesB x ⊹⊹ tracesB y
  tracesB (a LT b)  = tracesA a ⊹⊹ tracesA b

  traces : IExp → State → List Bhvr × State
  traces SKIP σ  = [] , σ
  traces (x ≔ n) σ with aexe n σ
  ... | N = (tracesA n) ⊹⊹ ((WRT x N) :: []) , set-var x N σ
  traces (e ⋯ e') σ with traces e σ
  ... | Bₑ , σ' with traces e' σ'
  ... | Bₑ' , σ'' = Bₑ ⊹⊹ Bₑ' , σ''
  traces (IF b THEN e ELSE e') σ with bexe b σ
  ... | true with traces e σ
  ... | Bₑ , σ' = tracesB b ⊹⊹ Bₑ , σ'   
  traces (IF b THEN e ELSE e') σ | false with traces e' σ
  ... | Bₑ' , σ'  = tracesB b ⊹⊹ Bₑ' , σ'
  traces (WHILE b DO c) σ = traces (IF b THEN (c ⋯ (WHILE b DO c)) ELSE SKIP) σ
  
  traces* : IExp → List Bhvr
  traces* i = traces i ⟦⟧ [0]
--}

