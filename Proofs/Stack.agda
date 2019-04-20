module Proofs.Stack where

  open import Lang.Stack
  open import Base.DataStructures
  open import Base.Inspect
  open import Data.Bool
  open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; +-comm; +-assoc)
  open import Data.Nat.Properties using (≤-refl)
  open import Misc.Base
  open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_)
  open import Data.Integer renaming (suc to zuc; _+_ to _z+_) hiding (_≤_; _>_; _<_)
  open import Agda.Builtin.Equality
  open import Data.Star
  open import Data.Nat.Base
  open import Data.Sign renaming (+ to ⊹)
  open import Data.String renaming (_≟_ to streqdec)
  open import Data.Maybe
  open import Data.Empty
  open import Proofs.Basic
  open import Proofs.NatProofs
  open import Relation.Binary
  open import Relation.Nullary using (¬_; Dec; yes; no)

  open import Semantics.LowLevel

  getFinalStoreᴸᴸ : ∀ {c' p c f f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → State
  getFinalStoreᴸᴸ {config σ _ _} m = σ

  &assoc : ∀ P Q R → P & Q & R ≡ (P & Q) & R
  &assoc [] Q R = refl
  &assoc (i :: is) Q R rewrite &assoc is Q R = refl

  insertAtEnd : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧
  insertAtEnd none w = some w none
  insertAtEnd (some one rest) w = some one (insertAtEnd rest w)

  insertAtEnd* : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒*⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧
  insertAtEnd* w none = w
  insertAtEnd* w (some one rest) = insertAtEnd* (insertAtEnd w one) rest

  fdecone : ∀ {p c f c' f'} → p ⊢⟦ c , (suc f) ⟧⇒⟦ c' , f' ⟧ → f' ≡ f
  fdecone (⊢LOADI x) = refl
  fdecone (⊢LOAD x₁) = refl
  fdecone (⊢STORE x₁) = refl
  fdecone (⊢ADD x) = refl
  fdecone (⊢JMP x) = refl
  fdecone (⊢JMPLESSfalse x x₁) = refl
  fdecone (⊢JMPLESStrue x x₁) = refl
  fdecone (⊢JMPGEtrue x x₁) = refl
  fdecone (⊢JMPGEfalse x x₁) = refl
  
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
  fdec {f = suc f} (some one rest) rewrite fdecone one = ≤s f (fdec rest)


  stacklem1a : ∀ p q {pc a} → p ፦ pc ≡ just a → p ፦ pc ≡ (p & q) ፦ pc
  stacklem1a [] _ ()
  stacklem1a p [] _ rewrite &[] {p} = refl
  stacklem1a (p :: ps) q {+ 0} _ = refl
  stacklem1a (p :: ps) q {+ (suc n)} x = stacklem1a ps q x
  stacklem1a (p :: ps) q { -[1+ n ]} ()

  stacklem1b : ∀ p q {pc a} → p ፦ pc ≡ just a → (p & q) ፦ pc ≡ just a
  stacklem1b p q j rewrite (sym j) = sym (stacklem1a p q j)


  stacklem1c : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧
  stacklem1c {p} {q} (⊢LOADI prf) = ⊢LOADI (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢LOAD prf) = ⊢LOAD (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢ADD prf) = ⊢ADD (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢STORE prf) = ⊢STORE (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMP prf) = ⊢JMP (stacklem1b p q prf)
  stacklem1c {p} {q} (⊢JMPLESStrue prf ltc) = ⊢JMPLESStrue (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPLESSfalse prf ltc) = ⊢JMPLESSfalse (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEtrue prf ltc) = ⊢JMPGEtrue (stacklem1b p q prf) ltc
  stacklem1c {p} {q} (⊢JMPGEfalse prf ltc) = ⊢JMPGEfalse (stacklem1b p q prf) ltc

  stacklem1 : ∀ {p q c c' f f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → (p & q) ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧
  stacklem1 none = none
  stacklem1 (some one then) = some (stacklem1c one) (stacklem1 then)

  


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


  pclem1 : ∀ {p q pc} → sign pc ≡ ⊹ → (p & q) ፦ (pc z+ size p) ≡ q ፦ pc
  pclem1 {[]} {q} {pc} _ rewrite +-identityʳ pc = refl
  pclem1 {x :: xs} {q} {+ n} prf rewrite +-comm (+ n) (size (x :: xs)) | +comm (size` xs) n = pclem1 {xs} {q} {+ n} prf
  pclem1 {x :: xs} {q} { -[1+ n ]} ()

  nofᴸ : ∀ {p f σ s pc σ' s' pc'} → p ⊢⟦ config σ s pc , 0 ⟧⇒*⟦ config σ' s' pc' , f ⟧ →  σ ≡ σ'
  nofᴸ none = refl
  nofᴸ (some () rest)

  noexec : ∀ {p f σ s pc σ' s' pc'} → p ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f ⟧ →  σ ≡ σ'
  noexec none = refl
  noexec {f = 0} (some () rest)
  noexec {f = suc f} (some one rest) with fdecone one | fdec rest
  ... | w | w' rewrite w = ⊥-elim (s≤→⊥ w') 

  just≡ : {i j : Inst} → _≡_ {A = Maybe Inst} (just i) (just j) → i ≡ j
  just≡ refl = refl

  detstep'nothing :  ∀ {x xs σ s pc f c' f'} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ → (x :: xs) ፦ pc ≡ nothing → ⊥
  detstep'nothing (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢STORE x) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢ADD x) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'nothing (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  LOADI≡ : ∀ {n n'} → LOADI n ≡ LOADI n' → n' ≡ n
  LOADI≡ {n} {n'} prf with Data.Nat.Base._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  LOADI≡ refl | no prf' = refl
  
  detstep'justloadi :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOADI n) → c'' ≡ c'
  detstep'justloadi (⊢LOADI x) (⊢LOADI y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOADI≡ w | LOADI≡ w' = refl
  detstep'justloadi (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justloadi (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justloadi (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justloadi sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justloadi sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  LOAD≡ : ∀ {x x'} → LOAD x ≡ LOAD x' → x' ≡ x
  LOAD≡ {x} {x'} prf with streqdec x x'
  ... | yes prfₙ = sym (prfₙ)
  LOAD≡ refl | no prf' = refl
  
  detstep'justload :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOAD n) → c'' ≡ c'
  detstep'justload (⊢LOAD x) (⊢LOAD y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOAD≡ w | LOAD≡ w' = refl
  detstep'justload (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justload (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justload (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justload sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justload sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justload sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  
  detstep'justadd :  ∀ {x xs σ s pc f c' f' c'' f''} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just ADD → c'' ≡ c'
  detstep'justadd (⊢ADD x) (⊢ADD y) prf = refl
  detstep'justadd (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justadd (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justadd (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justadd sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep'justadd sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justadd sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  STORE≡ : ∀ {x x'} → STORE x ≡ STORE x' → x' ≡ x
  STORE≡ {x} {x'} prf with streqdec x x'
  ... | yes prfₙ = sym (prfₙ)
  STORE≡ refl | no prf' = refl
  
  detstep'juststore :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (STORE n) → c'' ≡ c'
  detstep'juststore (⊢STORE x) (⊢STORE y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite STORE≡ w | STORE≡ w' = refl
  detstep'juststore (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'juststore (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'juststore (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep'juststore sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'juststore sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'juststore sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  JMP≡ : ∀ {n n'} → JMP n ≡ JMP n' → n' ≡ n
  JMP≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMP≡ refl | no prf' = refl
  
  detstep'justjmp :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMP n) → c'' ≡ c'
  detstep'justjmp (⊢JMP x) (⊢JMP y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMP≡ w | JMP≡ w' = refl
  detstep'justjmp (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmp (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmp (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmp sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmp sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  JMPGE≡ : ∀ {n n'} → JMPGE n ≡ JMPGE n' → n' ≡ n
  JMPGE≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMPGE≡ refl | no prf' = refl
  
  detstep'justjmpge :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPGE n) → c'' ≡ c'
  detstep'justjmpge (⊢JMPGEtrue x _) (⊢JMPGEtrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep'justjmpge (⊢JMPGEfalse x _) (⊢JMPGEfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep'justjmpge (⊢JMPGEfalse _ lt) (⊢JMPGEtrue _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpge (⊢JMPGEtrue _ ge) (⊢JMPGEfalse _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpge (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpge (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpge (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmpge sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmpge sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmpge sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmpge sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpge sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpge sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()

  JMPLESS≡ : ∀ {n n'} → JMPLESS n ≡ JMPLESS n' → n' ≡ n
  JMPLESS≡ {n} {n'} prf with Data.Integer._≟_ n n'
  ... | yes prfₙ = sym (prfₙ)
  JMPLESS≡ refl | no prf' = refl
  
  detstep'justjmpless :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPLESS n) → c'' ≡ c'
  detstep'justjmpless (⊢JMPLESStrue x _) (⊢JMPLESStrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep'justjmpless (⊢JMPLESSfalse x _) (⊢JMPLESSfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep'justjmpless (⊢JMPLESSfalse _ ge) (⊢JMPLESStrue _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpless (⊢JMPLESStrue _ lt) (⊢JMPLESSfalse _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpless (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpless (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpless (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmpless sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmpless sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmpless sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmpless sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpless sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpless sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()


  

  detstep : ∀ {x xs c f c' f' c'' f''} → (x :: xs) ⊢⟦ c , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ c , suc f ⟧⇒⟦ c'' , f'' ⟧ → c'' ≡ c'
  detstep {x} {xs} {config σ s pc} sem1 sem2 with inspect ((x :: xs) ፦ pc)
  ... | nothing with≡ prf = ⊥-elim (detstep'nothing sem1 prf)
  ... | (just i) with≡ prf with i
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOADI x₁ = detstep'justloadi sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOAD x₁ = detstep'justload sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | ADD = detstep'justadd sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | STORE x₁ = detstep'juststore sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMP x₁ = detstep'justjmp sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPLESS x₁ = detstep'justjmpless sem1 sem2 prf
  detstep {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPGE x₁ = detstep'justjmpge sem1 sem2 prf



  deterministic : ∀ {p c f σ' σ'' s' pc' f'} → p ⊢⟦ c , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ config σ'' s' pc' , f' ⟧ → σ'' ≡ σ'
  deterministic {[]} {config σ s pc} sem1 sem2 rewrite nothing≡σ sem1 | nothing≡σ sem2 = refl
  deterministic {x :: xs} {config σ s pc} none sem2 rewrite noexec sem2 = refl
  deterministic {x :: xs} {config σ s pc} sem1 none rewrite noexec sem1 = refl
  deterministic {x :: xs} {config σ s pc} {0} (some () rest)
  deterministic {x :: xs} {config σ s pc} {suc f} (some one rest) (some one' rest') rewrite fdecone one' | fdecone one | detstep one one' = deterministic rest rest'

  deterministic' : ∀ {p c f σ' σ'' s' s'' pc' pc'' f'} → p ⊢⟦ c , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ config σ'' s'' pc'' , f' ⟧ → σ'' ≡ σ'
  deterministic' {[]} {config σ s pc} sem1 sem2 rewrite nothing≡σ sem1 | nothing≡σ sem2 = refl
  deterministic' {x :: xs} {config σ s pc} none sem2 rewrite noexec sem2 = refl
  deterministic' {x :: xs} {config σ s pc} sem1 none rewrite noexec sem1 = refl
  deterministic' {x :: xs} {config σ s pc} {0} (some () rest)
  deterministic' {x :: xs} {config σ s pc} {suc f} (some one rest) (some one' rest') rewrite fdecone one' | fdecone one | detstep one one' = deterministic' rest rest'

  stacklem2b : ∀ p q {pc i} → q ፦ pc ≡ just i → (p & q) ፦ (pc z+ size p) ≡ just i
  stacklem2b [] q {pc} prf rewrite sym (prf) | z+0 pc = refl
  stacklem2b (i :: is) q {+ 0} prf rewrite 0+z (size (i :: is)) = stacklem2b is q prf
  stacklem2b (i :: is) q {+ (suc n)} prf rewrite +comm n (suc (size` is)) | +comm (size` is) n = stacklem2b is q prf
  stacklem2b (i :: is) [] { -[1+ _ ]} ()
  stacklem2b (i :: is) (q :: qs) { -[1+ _ ]} ()

  stacklem2c : ∀ p i is → (p & i :: is) ፦ (size p) ≡ just i
  stacklem2c [] i is = refl
  stacklem2c (x :: xs) i is = stacklem2c xs i is
  
  stacklem2a : ∀ p q {σ s f pc' σ' s' f'} → q ⊢⟦ config σ s (+ 0) , f ⟧⇒⟦ config σ' s' pc' , f' ⟧ → (p & q) ⊢⟦ config σ s (size p) , f ⟧⇒⟦ config σ' s' (size p z+ pc') , f' ⟧
  stacklem2a p q (⊢LOADI x) rewrite +comm (size` p) 1 = ⊢LOADI (stacklem2b p q x)
  stacklem2a p q (⊢LOAD x) rewrite +comm (size` p) 1 = ⊢LOAD (stacklem2b p q x)
  stacklem2a p q (⊢STORE x) rewrite +comm (size` p) 1 = ⊢STORE (stacklem2b p q x)
  stacklem2a p q (⊢ADD x) rewrite +comm (size` p) 1 = ⊢ADD (stacklem2b p q x)
  stacklem2a p q (⊢JMP {offset = o} x) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMP (stacklem2b p q x)
  stacklem2a p q (⊢JMPLESSfalse x x₁) rewrite +comm (size` p) 1 = ⊢JMPLESSfalse (stacklem2b p q x) x₁
  stacklem2a p q (⊢JMPLESStrue {offset = o} x x₁) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMPLESStrue ((stacklem2b p q x)) x₁
  stacklem2a p q (⊢JMPGEtrue {offset = o} x x₁) rewrite sym (+-assoc (size p) (+ 1) o) | +comm (size` p) 1 = ⊢JMPGEtrue ((stacklem2b p q x)) x₁
  stacklem2a p q (⊢JMPGEfalse x x₁) rewrite +comm (size` p) 1 = ⊢JMPGEfalse (stacklem2b p q x) x₁

{-
  stacklem2c : ∀ p i is {c c' f f'} → ((p & (i :: [])) & is) ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → (p & i :: is) ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ 
  stacklem2c = {!!}
-}
  stacklem2d : ∀ p n → size p z+ + suc n ≡ + suc ( size` p + n)
  stacklem2d [] n = refl
  stacklem2d (i :: is) n rewrite +comm (size` is) n | +comm (size` is) (suc n) = refl



  addF : ∀ {p c f c' f'}(n : ℕ) → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → p ⊢⟦ c , f + n ⟧⇒⟦ c' , f' + n ⟧
  addF n (⊢LOADI x) = ⊢LOADI x
  addF n (⊢LOAD x₁) = ⊢LOAD x₁
  addF n (⊢STORE x₁) = ⊢STORE x₁
  addF n (⊢ADD x) = ⊢ADD x
  addF n (⊢JMP x) = ⊢JMP x
  addF n (⊢JMPLESSfalse x x₁) = ⊢JMPLESSfalse x x₁
  addF n (⊢JMPLESStrue x x₁) = ⊢JMPLESStrue x x₁
  addF n (⊢JMPGEtrue x x₁) = ⊢JMPGEtrue x x₁
  addF n (⊢JMPGEfalse x x₁) = ⊢JMPGEfalse x x₁

  addF* : ∀ {p c f c' f'}(n : ℕ) → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , f + n ⟧⇒*⟦ c' , f' + n ⟧
  addF* n none = none
  addF* n (some one rest) = some (addF n one) (addF* n rest)

  sucF* : ∀ {p c f c' f'} → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → p ⊢⟦ c , suc f ⟧⇒*⟦ c' , suc f' ⟧
  sucF* {f = f} {f' = f'} x rewrite +comm 1 f | +comm 1 f' = addF* 1 x

  detstep' : ∀ {p f c c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ →  p ⊢⟦ c , f ⟧⇒⟦ c'' , f'' ⟧ → c'' ≡ c'
  detstep' {[]}  (⊢LOADI ()) sem2 
  detstep' {[]}  (⊢LOAD ()) sem2
  detstep' {[]}  (⊢STORE ()) sem2
  detstep' {[]}  (⊢ADD ()) sem2
  detstep' {[]}  (⊢JMP ()) sem2
  detstep' {[]}  (⊢JMPLESSfalse () x₁) sem2
  detstep' {[]}  (⊢JMPLESStrue () x₁) sem2
  detstep' {[]}  (⊢JMPGEtrue () x₁) sem2
  detstep' {[]}  (⊢JMPGEfalse () x₁) sem2
  detstep' {x :: xs} {0} sem1 sem2 with fdecone' sem1
  ... | ()
  detstep' {x :: xs} {suc f} sem1 sem2 = detstep sem1 sem2


  detstep'justloadi' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOADI n) → f'' ≡ f'
  detstep'justloadi' (⊢LOADI x) (⊢LOADI y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOADI≡ w | LOADI≡ w' = refl
  detstep'justloadi' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justloadi' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justloadi' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justloadi' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justloadi' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justloadi' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  detstep'justload' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (LOAD n) → f'' ≡ f'
  detstep'justload' (⊢LOAD x) (⊢LOAD y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite LOAD≡ w | LOAD≡ w' = refl
  detstep'justload' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justload' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justload' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justload' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justload' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justload' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  
  detstep'justadd' :  ∀ {x xs σ s pc f c' f' c'' f''} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just ADD → f'' ≡ f'
  detstep'justadd' (⊢ADD x) (⊢ADD y) prf = refl
  detstep'justadd' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justadd' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justadd' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justadd' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep'justadd' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justadd' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  detstep'juststore' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (STORE n) → f'' ≡ f'
  detstep'juststore' (⊢STORE x) (⊢STORE y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite STORE≡ w | STORE≡ w' = refl
  detstep'juststore' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'juststore' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'juststore' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | () 
  detstep'juststore' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'juststore' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'juststore' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  
  detstep'justjmp' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMP n) → f'' ≡ f'
  detstep'justjmp' (⊢JMP x) (⊢JMP y) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMP≡ w | JMP≡ w' = refl
  detstep'justjmp' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmp' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmp' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmp' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmp' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmp' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()

  
  detstep'justjmpge' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPGE n) → f'' ≡ f'
  detstep'justjmpge' (⊢JMPGEtrue x _) (⊢JMPGEtrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep'justjmpge' (⊢JMPGEfalse x _) (⊢JMPGEfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPGE≡ w | JMPGE≡ w' = refl
  detstep'justjmpge' (⊢JMPGEfalse _ lt) (⊢JMPGEtrue _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpge' (⊢JMPGEtrue _ ge) (⊢JMPGEfalse _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpge' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpge' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpge' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge' (⊢JMPLESSfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge' (⊢JMPLESStrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpge' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmpge' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmpge' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmpge' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmpge' sem1 (⊢JMPLESSfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpge' sem1 (⊢JMPLESStrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpge' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()
  
  detstep'justjmpless' :  ∀ {x xs σ s pc f c' f' c'' f'' n} → (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ config σ s pc , suc f ⟧⇒⟦ c'' , f'' ⟧ → (x :: xs) ፦ pc ≡ just (JMPLESS n) → f'' ≡ f'
  detstep'justjmpless' (⊢JMPLESStrue x _) (⊢JMPLESStrue y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep'justjmpless' (⊢JMPLESSfalse x _) (⊢JMPLESSfalse y _) prf rewrite prf with  sym (just≡ x) | sym (just≡ y)
  ... | w | w' rewrite JMPLESS≡ w | JMPLESS≡ w' = refl
  detstep'justjmpless' (⊢JMPLESSfalse _ ge) (⊢JMPLESStrue _ lt) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpless' (⊢JMPLESStrue _ lt) (⊢JMPLESSfalse _ ge) prf with ≤trans lt ge
  ... | w = ⊥-elim (s≤→⊥ w)
  detstep'justjmpless' (⊢LOAD x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless' (⊢STORE x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpless' (⊢ADD x) sem2 prf rewrite prf with x
  ... | () 
  detstep'justjmpless' (⊢LOADI x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless' (⊢JMPGEfalse x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless' (⊢JMPGEtrue x _) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless' (⊢JMP x) sem2 prf rewrite prf with x
  ... | ()
  detstep'justjmpless' sem1 (⊢LOAD x) prf rewrite prf with x
  ... | ()
  detstep'justjmpless' sem1 (⊢STORE x) prf rewrite prf with x
  ... | () 
  detstep'justjmpless' sem1 (⊢ADD x) prf rewrite prf with x
  ... | () 
  detstep'justjmpless' sem1 (⊢LOADI x) prf rewrite prf with x
  ... | ()
  detstep'justjmpless' sem1 (⊢JMPGEfalse x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpless' sem1 (⊢JMPGEtrue x _) prf rewrite prf with x
  ... | ()
  detstep'justjmpless' sem1 (⊢JMP x) prf rewrite prf with x
  ... | ()


  

  detstep'f : ∀ {x xs c f c' f' c'' f''} → (x :: xs) ⊢⟦ c , suc f ⟧⇒⟦ c' , f' ⟧ →  (x :: xs) ⊢⟦ c , suc f ⟧⇒⟦ c'' , f'' ⟧ → f'' ≡ f'
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 with inspect ((x :: xs) ፦ pc)
  ... | nothing with≡ prf = ⊥-elim (detstep'nothing sem1 prf)
  ... | (just i) with≡ prf with i
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOADI x₁ = detstep'justloadi' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | LOAD x₁ = detstep'justload' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | ADD = detstep'justadd' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | STORE x₁ = detstep'juststore' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMP x₁ = detstep'justjmp' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPLESS x₁ = detstep'justjmpless' sem1 sem2 prf
  detstep'f {x} {xs} {config σ s pc} sem1 sem2 | just i with≡ prf | JMPGE x₁ = detstep'justjmpge' sem1 sem2 prf

  detstep'f' : ∀ {p f c c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ →  p ⊢⟦ c , f ⟧⇒⟦ c'' , f'' ⟧ → f'' ≡ f'
  detstep'f' {[]}  (⊢LOADI ()) sem2 
  detstep'f' {[]}  (⊢LOAD ()) sem2
  detstep'f' {[]}  (⊢STORE ()) sem2
  detstep'f' {[]}  (⊢ADD ()) sem2
  detstep'f' {[]}  (⊢JMP ()) sem2
  detstep'f' {[]}  (⊢JMPLESSfalse () x₁) sem2
  detstep'f' {[]}  (⊢JMPLESStrue () x₁) sem2
  detstep'f' {[]}  (⊢JMPGEtrue () x₁) sem2
  detstep'f' {[]}  (⊢JMPGEfalse () x₁) sem2
  detstep'f' {x :: xs} {0} sem1 sem2 with fdecone' sem1
  ... | ()
  detstep'f' {x :: xs} {suc f} sem1 sem2 = detstep'f sem1 sem2

  spliton' : ∀ {p c f c' f' c'' f''} → ¬ f ≡ f'' → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒⟦ c' , f' ⟧ → p ⊢⟦ c' , f' ⟧⇒*⟦ c'' , f'' ⟧
  spliton' w none x' = ⊥-elim (w refl)
  spliton' _ (some x w) x' rewrite detstep' x' x | detstep'f' x' x = w


  split_on_⊢ : ∀ {p c f c' f' c'' f''} → p ⊢⟦ c , f ⟧⇒*⟦ c'' , f'' ⟧ → p ⊢⟦ c , f ⟧⇒*⟦ c' , f' ⟧ → f'' ≤ f' → p ⊢⟦ c' , f' ⟧⇒*⟦ c'' , f'' ⟧
  split w on none ⊢ _ = w
  split none on (some one rest) ⊢ w with ≤trans (≤trans (s≤s (fdec rest)) (fdecone' one)) w
  ... | z = ⊥-elim (s≤→⊥ z)
  split (some one' rest') on (some one rest) ⊢ w with ≤trans (s≤s (fdec rest')) (fdecone' one')
  ... | z = split spliton' (s≤→¬≡ z) (some one' rest') one on rest ⊢ w

--≤trans (s≤s (fdec rest')) (fdecone' one')
--  ... | w = split (spliton' (s≤→¬≡ w) (some one' rest') one) on rest

  
  stacklem2a' : ∀ p q {σ s f pc pc' σ' s'} → q ⊢⟦ config σ s pc , suc f ⟧⇒⟦ config σ' s' pc' , f ⟧ → (p & q) ⊢⟦ config σ s (pc z+ size p) , suc f ⟧⇒⟦ config σ' s' (pc' z+ size p) , f ⟧
  stacklem2a' p q (⊢LOADI x) = ⊢LOADI (stacklem2b p q x)
  stacklem2a' p q (⊢LOAD x) = ⊢LOAD (stacklem2b p q x)
  stacklem2a' p q (⊢STORE x) = ⊢STORE (stacklem2b p q x)
  stacklem2a' p q (⊢ADD x) = ⊢ADD (stacklem2b p q x)
  stacklem2a' p q {pc = (+ pc)} (⊢JMP {offset = o} x) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o) = ⊢JMP (stacklem2b p q x)
  stacklem2a' p q (⊢JMPLESSfalse x x₁) = ⊢JMPLESSfalse (stacklem2b p q x) x₁
  stacklem2a' p q {pc = (+ pc)} (⊢JMPLESStrue {offset = o} x x₁) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o) = ⊢JMPLESStrue ((stacklem2b p q x)) x₁
  stacklem2a' p q {pc = (+ pc)} (⊢JMPGEtrue {offset = o} x x₁) rewrite +-assoc (+ suc pc) o (+ size` p) | +-comm o (+ size` p) | sym ( +-assoc (+ suc pc) (+ size` p) o) = ⊢JMPGEtrue ((stacklem2b p q x)) x₁
  stacklem2a' p q (⊢JMPGEfalse x x₁) = ⊢JMPGEfalse (stacklem2b p q x) x₁

  stacklem2aux1 : ∀ {q a f σ s pc σ' s' pc'} → q ⊢⟦ config σ s pc , suc f ⟧⇒⟦ config σ' s' pc' , a ⟧ → a ≡ f → q ⊢⟦ config σ s pc , suc f ⟧⇒⟦ config σ' s' pc' , f ⟧
  stacklem2aux1 sem prf rewrite prf = sem

  stacklem2aux2 : ∀ {q a f σ' s' pc' σ'' s'' pc'' f'} → q ⊢⟦ config σ' s' pc' , a ⟧⇒*⟦ config σ'' s'' pc'' , f' ⟧ → a ≡ f → q ⊢⟦ config σ' s' pc' , f ⟧⇒*⟦ config σ'' s'' pc'' , f' ⟧
  stacklem2aux2 sem prf rewrite prf = sem
 
  stacklem2 : ∀ p q {σ s f pc pc' σ' s' f'} → q ⊢⟦ config σ s pc , f ⟧⇒*⟦ config σ' s' pc' , f' ⟧ → (p & q) ⊢⟦ config σ s (pc z+ size p) , f ⟧⇒*⟦ config σ' s' (pc' z+ size p) , f' ⟧
  stacklem2 p q none = none
  stacklem2 p q (some {c = config σ s pc} {config σ' s' pc'} {config σ'' s'' pc''} {suc f} {a} one rest) = some {c = config σ s (pc z+ size p)} {config σ' s' (pc' z+ size p)} (stacklem2a' p q {pc = pc} {pc'} (stacklem2aux1 one (fdecone one))) (stacklem2 p q {f = f} {pc'} {pc''} (stacklem2aux2 rest (fdecone one)))
  stacklem2 p q {f = 0} (some () rest)

{-
  stacklem2 [] q {pc' = pc} semq rewrite +-identityˡ pc = semq
  stacklem2 (i :: is) q semq = {!!}
  -}


  
