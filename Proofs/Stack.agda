module Proofs.Stack where

  open import Lang.Stack
  
  open import Base.DataStructures
  open import Base.Inspect
  
  open import Misc.Base
  
  open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_)
  open import Agda.Builtin.Equality
  
  open import Data.Nat.Base
  open import Data.String renaming (_≟_ to streqdec)
  open import Data.Maybe
  open import Data.Empty
  open import Data.Bool
  open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; +-comm; +-assoc)
  open import Data.Nat.Properties using (≤-refl; ≤-trans)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_; _<_)
  
  open import Proofs.Basic
  open import Proofs.NatProofs
  
  open import Relation.Binary
  open import Relation.Nullary using (¬_; Dec; yes; no)

  open import Semantics.LowLevel

  --------------------------------------
  -- Proofs about low level semantics --
  --------------------------------------

    --------------------------------------------------------
    -- Transitive composition of SML small-step semantics --
    --------------------------------------------------------

  TransComp : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧
  TransComp none w = some w none
  TransComp (some one rest) w = some one (TransComp rest w)

  TransComp* : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒*⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧
  TransComp* w none = w
  TransComp* w (some one rest) = TransComp* (TransComp w one) rest

    ------------------------------------------------------------------------------
    -- Adding more instructions to a program does not change existing semantics --
    ------------------------------------------------------------------------------

  stacklem1a : ∀ p q {pc a} → p ፦ pc ≡ just a → p ፦ pc ≡ (p & q) ፦ pc
  stacklem1a []        _             ()
  stacklem1a (p :: ps) q {+ 0}       _  = refl
  stacklem1a (p :: ps) q {+ (suc n)} x  = stacklem1a ps q x
  stacklem1a (p :: ps) q { -[1+ n ]} ()

  stacklem1b : ∀ p q {pc a} → p ፦ pc ≡ just a → (p & q) ፦ pc ≡ just a
  stacklem1b p q j rewrite (sym j) = sym (stacklem1a p q j)

  stacklem1c : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧
  stacklem1c {p} {q} (⊢LOADI        prf)     = ⊢LOADI        (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢LOAD         prf)     = ⊢LOAD         (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢ADD          prf)     = ⊢ADD          (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢STORE        prf)     = ⊢STORE        (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMP          prf)     = ⊢JMP          (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMPLESStrue  prf ltc) = ⊢JMPLESStrue  (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPLESSfalse prf ltc) = ⊢JMPLESSfalse (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEtrue    prf ltc) = ⊢JMPGEtrue    (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEfalse   prf ltc) = ⊢JMPGEfalse   (stacklem1b p q prf) ltc

  -- Appending another program 
  stacklem1 : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  stacklem1 none = none
  stacklem1 (some one then) = some (stacklem1c one) (stacklem1 then)

  -- Executing a single instruction always reduces the fuel by one. --
  fdecone : ∀ {p c f c' f'} → p ⊢⟦ c , (suc f) ⟧⇒⟦ c' , f' ⟧ → f' ≡ f
  fdecone (⊢LOADI x)           = refl
  fdecone (⊢LOAD x₁)           = refl
  fdecone (⊢STORE x₁)          = refl
  fdecone (⊢ADD x)             = refl
  fdecone (⊢JMP x)             = refl
  fdecone (⊢JMPLESSfalse x x₁) = refl
  fdecone (⊢JMPLESStrue x x₁)  = refl
  fdecone (⊢JMPGEtrue x x₁)    = refl
  fdecone (⊢JMPGEfalse x x₁)   = refl
  
  stacklem2c : ∀ p i is → (p & i :: is) ፦ (size p) ≡ just i
  stacklem2c [] i is = refl
  stacklem2c (x :: xs) i is = stacklem2c xs i is
  
  stacklem2b : ∀ p q {pc i} → q ፦ pc ≡ just i → (p & q) ፦ (pc z+ size p) ≡ just i
  stacklem2b [] q {pc} prf rewrite sym (prf) | z+0 pc = refl
  stacklem2b (i :: is) q {+ 0} prf rewrite 0+z (size (i :: is)) = stacklem2b is q prf
  stacklem2b (i :: is) q {+ (suc n)} prf rewrite +comm n (suc (size` is)) | +comm (size` is) n = stacklem2b is q prf
  stacklem2b (i :: is) [] { -[1+ _ ]} ()
  stacklem2b (i :: is) (q :: qs) { -[1+ _ ]} ()

  stacklem2b' : ∀ p {q pc i} →  q ፦ (+ pc) ≡ just i → (p & q) ፦ (+ (size` p + pc)) ≡ just i
  stacklem2b' p {pc = pc} p1 rewrite +comm (size` p) pc = stacklem2b p _ p1
  
  -- Prepending a program for a single step.
  stacklem2a : ∀ p q {σ s f pc pc' σ' s'} → q ⊢⟦ config σ s pc , suc f ⟧⇒⟦ config σ' s' pc' , f ⟧ → (p & q) ⊢⟦ config σ s (pc z+ size p) , suc f ⟧⇒⟦ config σ' s' (pc' z+ size p) , f ⟧
  stacklem2a p q (⊢LOADI x)           = ⊢LOADI (stacklem2b p q x)
  stacklem2a p q (⊢LOAD x)            = ⊢LOAD (stacklem2b p q x)
  stacklem2a p q (⊢STORE x)           = ⊢STORE (stacklem2b p q x)
  stacklem2a p q (⊢ADD x)             = ⊢ADD (stacklem2b p q x)
  
  stacklem2a p q {pc = (+ pc)} (⊢JMP {offset = o} x) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o)
                                      = ⊢JMP (stacklem2b p q x)
  
  stacklem2a p q (⊢JMPLESSfalse x x₁) = ⊢JMPLESSfalse (stacklem2b p q x) x₁
  
  stacklem2a p q {pc = (+ pc)} (⊢JMPLESStrue {offset = o} x x₁) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o)
                                      = ⊢JMPLESStrue (stacklem2b p q x) x₁
  
  stacklem2a p q {pc = (+ pc)} (⊢JMPGEtrue {offset = o} x x₁) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o)
                                      = ⊢JMPGEtrue  (stacklem2b p q x) x₁
  
  stacklem2a p q (⊢JMPGEfalse x x₁)   = ⊢JMPGEfalse (stacklem2b p q x) x₁

  -- Prepending for a chain of semantic steps
  -- Prepending increments the program counter by the amount of instructions added. --
  stacklem2 : ∀ p q {σ s f pc pc' σ' s' f'} → q ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → (p & q) ⊢⟦ config σ s (pc z+ size p) , f ⟧⇒*⟦ config σ' s' (pc' z+ size p) , f' ⟧
  stacklem2 p q none = none
  stacklem2 p q (some {c' = config σ' s' pc'} {f = suc f} one rest) with fdecone one
  ... | refl = some (stacklem2a p q one) (stacklem2 p q rest)
  stacklem2 p q {f = 0} (some () rest)  



  -----------------------
  -- Proofs about fuel --
  -----------------------
  
  fdecone' : ∀ {p c f c' f'} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → f' < f
  fdecone' (⊢LOADI x)           = ≤-refl
  fdecone' (⊢LOAD x₁)           = ≤-refl
  fdecone' (⊢STORE x₁)          = ≤-refl
  fdecone' (⊢ADD x)             = ≤-refl
  fdecone' (⊢JMP x)             = ≤-refl 
  fdecone' (⊢JMPLESSfalse x x₁) = ≤-refl 
  fdecone' (⊢JMPLESStrue x x₁)  = ≤-refl
  fdecone' (⊢JMPGEtrue x x₁)    = ≤-refl
  fdecone' (⊢JMPGEfalse x x₁)   = ≤-refl

  fdec : ∀ {p c f c' f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → f' ≤ f
  fdec none = ≤=
  fdec {f = 0} (some () rest)
  fdec {f = suc f} (some one rest) = ≤-trans (≤s _ (fdec rest)) (fdecone' one)



    ----------------------------------
    -- Adding and substracting fuel --
    ----------------------------------


  addF : ∀ {p c f c' f'}(n : ℕ) → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → p ⊢⟦ c , f + n ⟧⇒⟦ c' , f' + n ⟧
  addF n (⊢LOADI x)           = ⊢LOADI x
  addF n (⊢LOAD x₁)           = ⊢LOAD x₁
  addF n (⊢STORE x₁)          = ⊢STORE x₁
  addF n (⊢ADD x)             = ⊢ADD x
  addF n (⊢JMP x)             = ⊢JMP x
  addF n (⊢JMPLESSfalse x x₁) = ⊢JMPLESSfalse x x₁
  addF n (⊢JMPLESStrue x x₁)  = ⊢JMPLESStrue x x₁
  addF n (⊢JMPGEtrue x x₁)    = ⊢JMPGEtrue x x₁
  addF n (⊢JMPGEfalse x x₁)   = ⊢JMPGEfalse x x₁

  decF : ∀ {p c f c' f'} → p ⊢⟦ c , suc f ⟧⇒⟦ c' , suc f' ⟧ → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧
 
  decF  (⊢LOADI x) = ⊢LOADI x
  decF  (⊢LOAD x₁) = ⊢LOAD x₁
  decF  (⊢STORE x₁) = ⊢STORE x₁
  decF  (⊢ADD x) = ⊢ADD x
  decF  (⊢JMP x) = ⊢JMP x
  decF  (⊢JMPLESSfalse x x₁) = ⊢JMPLESSfalse x x₁
  decF  (⊢JMPLESStrue x x₁) = ⊢JMPLESStrue x x₁
  decF  (⊢JMPGEtrue x x₁) = ⊢JMPGEtrue x x₁
  decF  (⊢JMPGEfalse x x₁) = ⊢JMPGEfalse x x₁

  subF : ∀ {p c f c' f'}(n : ℕ)(ineq : 0 < f) → p ⊢⟦ c , f + n ⟧⇒⟦ c' , f' + n ⟧ → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧
  subF {f = 0} _ ()
  subF {f = suc f} {f' = f'} 0 ineq stp rewrite +comm f 0 | +comm f' 0 = stp
  subF {f = suc f} {f' = f'} (suc n) ineq stp rewrite sym (+swap {f} {n}) | sym (+swap {f'} {n}) = subF n ineq (decF stp)
  
  addF* : ∀ {p c f c' f'}(n : ℕ) → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , f + n ⟧⇒*⟦ c' , f' + n ⟧
  addF* n none = none
  addF* n (some one rest) = some (addF n one) (addF* n rest)

  addF*' : ∀ {p c f c' f'}(n : ℕ) → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , n + f ⟧⇒*⟦ c' , n + f' ⟧
  addF*' {f = f} {f' = f'} n sem rewrite +comm n f | +comm n f' = addF* n sem 
  
  sucF* : ∀ {p c f c' f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , suc f ⟧⇒*⟦ c' , suc f' ⟧
  sucF* {f = f} {f' = f'} x rewrite +comm 1 f | +comm 1 f' = addF* 1 x

  dec'F* :  ∀ {p c f c' f'} → p ⊢⟦ c , suc f ⟧⇒*⟦ c' , suc f' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  dec'F* none = none
  dec'F* {f = suc f} (some one rest) with fdecone one
  ... | z rewrite z  = some (decF one) (dec'F* rest)
  dec'F* {f = zero} (some one rest) with fdecone one
  ... | z rewrite z with fdec rest
  ... | ()

  subF* : ∀ {p c f c' f'} n → p ⊢⟦ c , n + f ⟧⇒*⟦ c' , n + f' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  subF* 0 sem = sem
  subF* (suc n) sem = subF* n (dec'F* sem)

  subF*' : ∀ {p c f c' f'} n → p ⊢⟦ c , f + n ⟧⇒*⟦ c' , f' + n ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  subF*' {f = f} {f' = f'} n sem rewrite +comm f n | +comm f' n = subF* n sem


  ------------------
  -- No execution --
  ------------------

  nothing≡pc : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → pc ≡ pc'
  nothing≡pc none = refl
  nothing≡pc (some (⊢LOADI ()) _)
  nothing≡pc (some (⊢LOAD ()) _)
  nothing≡pc (some (⊢ADD ()) _)
  nothing≡pc (some (⊢STORE ()) _)
  nothing≡pc (some (⊢JMP ()) _)
  nothing≡pc (some (⊢JMPLESStrue () _) _)
  nothing≡pc (some (⊢JMPGEtrue () _) _)
  nothing≡pc (some (⊢JMPLESSfalse () _) _)
  nothing≡pc (some (⊢JMPGEfalse () _) _)


  nothing≡s : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → s ≡ s'
  nothing≡s none = refl
  nothing≡s (some (⊢LOADI ()) _)
  nothing≡s (some (⊢LOAD ()) _)
  nothing≡s (some (⊢ADD ()) _)
  nothing≡s (some (⊢STORE ()) _)
  nothing≡s (some (⊢JMP ()) _)
  nothing≡s (some (⊢JMPLESStrue () _) _)
  nothing≡s (some (⊢JMPGEtrue () _) _)
  nothing≡s (some (⊢JMPLESSfalse () _) _)
  nothing≡s (some (⊢JMPGEfalse () _) _)

  nothing≡σ : ∀ {σ s pc σ' s' pc' f f'} → [] ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → σ ≡ σ'
  nothing≡σ none = refl
  nothing≡σ (some (⊢LOADI ()) _)
  nothing≡σ (some (⊢LOAD ()) _)
  nothing≡σ (some (⊢ADD ()) _)
  nothing≡σ (some (⊢STORE ()) _)
  nothing≡σ (some (⊢JMP ()) _)
  nothing≡σ (some (⊢JMPLESStrue () _) _)
  nothing≡σ (some (⊢JMPGEtrue () _) _)
  nothing≡σ (some (⊢JMPLESSfalse () _) _)
  nothing≡σ (some (⊢JMPGEfalse () _) _)

  nothing≡c : ∀ {c f c' f'} → [] ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → c ≡ c'
  nothing≡c none = refl
  nothing≡c (some (⊢LOADI ()) _)
  nothing≡c (some (⊢LOAD ()) _)
  nothing≡c (some (⊢ADD ()) _)
  nothing≡c (some (⊢STORE ()) _)
  nothing≡c (some (⊢JMP ()) _)
  nothing≡c (some (⊢JMPLESStrue () _) _)
  nothing≡c (some (⊢JMPGEtrue () _) _)
  nothing≡c (some (⊢JMPLESSfalse () _) _)
  nothing≡c (some (⊢JMPGEfalse () _) _)

  nothing≡f : ∀ {c f c' f'} → [] ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → f ≡ f'
  nothing≡f none = refl
  nothing≡f (some (⊢LOADI ()) _)
  nothing≡f (some (⊢LOAD ()) _)
  nothing≡f (some (⊢ADD ()) _)
  nothing≡f (some (⊢STORE ()) _)
  nothing≡f (some (⊢JMP ()) _)
  nothing≡f (some (⊢JMPLESStrue () _) _)
  nothing≡f (some (⊢JMPGEtrue () _) _)
  nothing≡f (some (⊢JMPLESSfalse () _) _)
  nothing≡f (some (⊢JMPGEfalse () _) _)

  nofᴸ : ∀ {p f σ s pc σ' s' pc'} → p ⊢⟦ config σ s pc , 0 ⟧⇒*⟦ config σ' s' pc' , f ⟧ →  σ ≡ σ'
  nofᴸ none = refl
  nofᴸ (some () rest)

  noexec : ∀ {p f σ s pc σ' s' pc'} → p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f ⟧ →  σ ≡ σ'
  noexec none = refl
  noexec {f = 0} (some () rest)
  noexec {f = suc f} (some one rest) with fdecone one | fdec rest
  ... | w | w' rewrite w = ⊥-elim (s≤→⊥ w')
