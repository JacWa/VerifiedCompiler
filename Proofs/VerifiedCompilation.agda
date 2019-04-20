module Proofs.VerifiedCompilation where

  open import Proofs.NatProofs
  open import Proofs.Expr
  open import Proofs.Stack
  open import Proofs.ArithSemantics
  open import Proofs.Fuel
  open import Proofs.Bool
  open import Proofs.Compiler
  open import Proofs.SeqComp

  open import Semantics.Build
  open import Semantics.LowLevel
  open import Semantics.HighLevel

  open import Lang.Expr renaming (_≟_ to _≟ⁱ_)
  open import Lang.Stack

  open import Compiler

  open import Agda.Builtin.Sigma using (fst; snd; Σ) renaming (_,_ to _∣_)
  open import Agda.Builtin.Nat using (_<_)
  open import Base.Inspect
  open import Base.Tuple using (l; r; _×_) renaming (_,_ to _~_)
  open import Base.Existential

  open import Data.Nat using (suc; _≤_) renaming (_+_ to _ℕ+_)
  open import Data.Integer using (+_) renaming (_+_ to _ℤ+_; suc to zuc)
  open import Data.Bool using (true; false; _≟_)
  open import Data.Maybe
  open import Data.Empty
  

  open import Base.DataStructures
  open import Base.Or
  open import Misc.Base hiding (_∧_; fst; snd; _×_; _,_)

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Relation.Binary
  open import Relation.Nullary



  mutual
    Lemma2 : ∀ b Q {f s σ} → bexe b σ ≡ false → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b false σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q) & Q)) , f ⟧
    Lemma2 (BOOL x) y z rewrite z = some (⊢JMP refl) none
    Lemma2 (NOT x) y z = Lemma2' x y (notfalse z)
    Lemma2 (a AND b) y {f} {s} {σ} z rewrite sym (&assoc (bcomp a false (+ (size` (bcomp b false (size y)) ℕ+ size` y))) (bcomp b false (size y)) y) with bexe a σ ≟ false
    ... | yes prf rewrite sym (size`&+ {bcomp b false (+ size` y)} {y}) | size`&+ {bcomp a false (+ size` (bcomp b false (+ size` y) & y))} {bcomp b false (+ size` y)} | sym (+assoc (size` (bcomp a false (+ size` (bcomp b false (+ size` y) & y)))) (size` (bcomp b false (+ size` y))) f) | prf | sym (size`&+ {bcomp b false (+ size` y)} {y}) = Lemma2 a (bcomp b false (+ size` y) & y) prf
    ... | no prf with ∧-false prf z | ¬-false prf
    ... | w | w' rewrite w' with Lemma3 a (bcomp b false (+ size` y) & y) {(fuelLLb b false σ (+ size` y) ℕ+ f)} {s} {σ} w'
    ... | w'' rewrite sym (+assoc (fuelLLb a false σ (+ (size` (bcomp b false (+ size` y)) ℕ+ size` y))) (fuelLLb b false σ (size y)) f) | size`&+ {bcomp b false (+ size` y)} {y} with bcomp a false (+ (size` (bcomp b false (+ size` y)) ℕ+ size` y))
    ... | A rewrite size`&+ {A} {bcomp b false (+ size` y) & y} | +comm (size` A) (size` (bcomp b false (+ size` y) & y)) = insertAtEnd* w'' (stacklem2 A (bcomp b false (+ size` y) & y) (Lemma2 b y w))
    Lemma2 (a LT b) y {f} {s} {σ} z rewrite sym (&assoc (acomp a) (acomp b & JMPGE (size y) :: []) y) | sym (&assoc (acomp b) (JMPGE (size y) :: []) y) | size`&+ {acomp a} {acomp b & JMPGE (+ size` y) :: []} | sym (+assoc (size` (acomp a)) (size` (acomp b & JMPGE (+ size` y) :: [])) f) with ArithExec {a} {[]} {acomp b & JMPGE (+ size` y) :: y} {σ} {s} {(size` (acomp b) ℕ+ 1) ℕ+ f}
    ... | w rewrite +assoc (size` (acomp a)) (size` (acomp b) ℕ+ 1) f | sym (size`&+ {acomp b} {JMPGE (+ size` y) :: []}) = insertAtEnd* w (insertAtEnd (Lemma2Aux1 {a} {b}) (Lemma2Aux2 {a} {b}))


    Lemma2' : ∀ b Q {f s σ} → bexe b σ ≡ true → (bcomp b true (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b true σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b true (size Q) & Q)) , f ⟧
    Lemma2' (BOOL x) y z rewrite z = some (⊢JMP refl) none
    Lemma2' (NOT x) y z = Lemma2 x y (nottrue z)
    Lemma2' (a AND b) y {f} {s} {σ} z with bexe a σ ≟ true
    ... | no prf = ⊥-elim (∧-true prf z)
    ... | yes prf rewrite prf | sym (+assoc (fuelLLb a false σ (+ size` (bcomp b true (+ size` y)))) (fuelLLb b true σ (+ size` y)) f) with Lemma2' b y {f} {s} {σ} z
    ... | w = insertAtEnd* (stacklem1 (Lemma3 a (bcomp b true (+ size` y)) prf)) (Lemma2'Aux1 {a} {b} {y} (stacklem2 (bcomp a false (+ size` (bcomp b true (+ size` y)))) ((bcomp b true (+ size` y)) & y) {pc = + 0} w))
    Lemma2' (a LT b) y {f} {s} {σ} z with stacklem1 {q = y} (Lemma1' {a} {acomp b & JMPLESS (size y) :: []} {σ} {s} {f})
    ... | w rewrite sym (&assoc (acomp a) (acomp b & JMPLESS (+ size` y) :: []) (y)) | sym (&assoc (acomp b) (JMPLESS (+ size` y) :: []) y) | sym (size`&+ {acomp b} {JMPLESS (+ size` y) :: []}) | sym (size`&+ {acomp a} {acomp b & JMPLESS (+ size` y) :: []}) with ArithExec {b} {acomp a} {JMPLESS (+ size` y) :: y} {σ} {aexe a σ , s} {suc f}
    ... | w' rewrite size`&+ {acomp b} {JMPLESS (+ size` y) :: []} | sym (+assoc (size` (acomp b)) 1 f) = insertAtEnd* w (insertAtEnd w' (Lemma2'Aux2 {a} {b} z))
    
    Lemma2'Aux1 : ∀ {a b y σ s f} → ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y) & y) ⊢⟦ config σ s (+ size` (bcomp a false (+ size` (bcomp b true (+ size` y))))) , fuelLLb b true σ (+ size` y) ℕ+ f ⟧⇒*⟦ config σ s (+ (size` (bcomp b true (+ size` y) & y) ℕ+ size` (bcomp a false (+ size` (bcomp b true (+ size` y)))))) , f ⟧) → ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y)) & y) ⊢⟦ config σ s (size (bcomp a false (size (bcomp b true (+ size` y))))) , fuelLLb b true σ (+ size` y) ℕ+ f ⟧⇒*⟦ config σ s (+ size` ((bcomp a false (+ size` (bcomp b true (+ size` y))) & bcomp b true (+ size` y)) & y)) , f ⟧
    Lemma2'Aux1 {a} {b} {y} {σ} {s} {f} sem with bcomp b true (+ size` y)
    ... | B with (bcomp a false (+ size` B))
    ... | A rewrite +comm (size` (B & y)) (size` A) | sym (size`&+ {A} {B & y}) | &assoc A B y = sem

    Lemma2'Aux2 : ∀ {a} {b} {y} {σ} {s} {f} → (aexe a σ < aexe b σ) ≡ true → (acomp a & acomp b & JMPLESS (+ size` y) :: y) ⊢⟦ config σ (aexe b σ , aexe a σ , s) (+ size` (acomp b & acomp a)) , suc f ⟧⇒⟦ config σ s (+ size` (acomp a & acomp b & JMPLESS (+ size` y) :: y)) , f ⟧
    Lemma2'Aux2 {a} {b} {y} {σ} {s} {f} z with stacklem2c (acomp a & acomp b) (JMPLESS (size y)) y
    ... | w rewrite &assoc (acomp a) (acomp b) (JMPLESS (size y) :: y) | size`trans (acomp a) (acomp b) with ⊢JMPLESStrue {((acomp a & acomp b) & JMPLESS (+ size` y) :: y)} {σ} {s} {aexe b σ} {aexe a σ} {(size` (acomp b & acomp a))} {size y} {f} w (<-true z)
    ... | w' rewrite sym (&assoc (acomp a) (acomp b) (JMPLESS (+ size` y) :: y)) | size`&+3/4 (acomp a) (acomp b) (JMPLESS (+ size` y) :: []) y | &assoc (acomp a) (acomp b) y | size`&+ {acomp a & acomp b} {y} | size`trans (acomp a) (acomp b) = w'
    
    postulate
      Lemma2Aux1 : ∀ {a} {b} {y} {σ} {s} {f} → (acomp a & acomp b & JMPGE (+ size` y) :: y) ⊢⟦ config σ (aexe a σ , s) (size (acomp a & [])) , size` (acomp b & JMPGE (+ size` y) :: []) ℕ+ f ⟧⇒*⟦ config σ (aexe b σ , aexe a σ , s) (size (acomp a & acomp b)) , size` (JMPGE (+ size` y) :: []) ℕ+ f ⟧
      Lemma2Aux2 : ∀ {a} {b} {y} {σ} {s} {f} → (acomp a & acomp b & JMPGE (+ size` y) :: y) ⊢⟦ config σ (aexe b σ , aexe a σ , s) (size (acomp a & acomp b)) , size` (JMPGE (+ size` y) :: []) ℕ+ f ⟧⇒⟦ config σ s (+ size` (acomp a & acomp b & JMPGE (+ size` y) :: y)) , f ⟧
      Lemma3 : ∀ b Q {f s σ} → bexe b σ ≡ true  → (bcomp b false (size Q) & Q) ⊢⟦ config σ s (+ 0) , (fuelLLb b false σ (size Q)) ℕ+ f ⟧⇒*⟦ config σ s (size (bcomp b false (size Q))) , f ⟧
  postulate
    Lemma4 : ∀ {c} {b} {σ} → bexe b σ ≡ false → size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ≡ fuelLLb b false σ (_ℤ+_ (size (compile c)) (+ 1))

    Lemma5 : ∀ {c b f σ σᴴᴸ σᴸᴸ f'}(rest : ⟦ σ , c ⋯ (WHILE b DO c) , f ⟧↦*⟦ σᴴᴸ , SKIP , f' ⟧) → (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) ⊢⟦ config σ $ (+ 0) , fuelLLb b false σ (+ (size` (compile c) ℕ+ 1)) ℕ+ fuelLL (c ⋯ (WHILE b DO c)) f rest ⟧⇒*⟦ config σᴸᴸ $ (+ size` (bcomp b false (+ (size` (compile c) ℕ+ 1)) & compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: [])) , f' ⟧ → (compile c & (compile (WHILE b DO c))) ⊢⟦ config σ $ (+ 0) , fuelLL (c ⋯ (WHILE b DO c)) f rest ⟧⇒*⟦ config σᴸᴸ $ (size (compile c & (compile (WHILE b DO c)))) , f' ⟧



  Lemma6 : ∀ {P P' Q σ σ' σᴴᴸ σᴸᴸ f f'} → (one : ⟦ σ , P , suc f ⟧↦⟦ σ' , P' , f ⟧)(rest :  ⟦ σ' , P' ⋯ Q , f ⟧↦*⟦ σᴴᴸ , SKIP , f' ⟧) → (compile P & compile Q) ⊢⟦ config σ $ (+ 0) , fuelLL' (P ⋯ Q) (seqstep one) ℕ+ fuelLL (P' ⋯ Q) f rest ⟧⇒*⟦ config σᴸᴸ $ (+ size` (compile P & compile Q)) , f' ⟧ → (compile P' & compile Q) ⊢⟦ config σ' $ (+ 0) , fuelLL (P' ⋯ Q) f rest ⟧⇒*⟦ config σᴸᴸ $ (size (compile P' & compile Q)) , f' ⟧
  Lemma6 {f = Data.Nat.zero} one rest w with nofᴴf rest
  ... | z rewrite z = {!!}
  Lemma6 {f = suc f} one rest w = {!!}
    
-----------------
-- Final Proof --
-----------------


  Lemma : ∀ I {σ f σᴴᴸ σᴸᴸ} → (semᴴᴸ : ⟦ σ , I , f ⟧↦*⟦ σᴴᴸ , SKIP , 0 ⟧) → compile I ⊢⟦ config σ $ (+ 0) , fuelLL I f semᴴᴸ ⟧⇒*⟦ config σᴸᴸ $ (size (compile I)) , 0 ⟧ → σᴸᴸ ≡ σᴴᴸ
  Lemma _ {f = 0} x w rewrite nofᴴ x | nofᴸ w = refl
  Lemma (SKIP) {f = suc f} (step () _)
  Lemma (x ≔ a) {σ} {f = suc 0} (step assign rest) w rewrite fuelSKIP 0 {rest = rest} | skipseqσ rest | skipseqf rest |  size`&+ {acomp a} {STORE x :: []} | +comm (size` (acomp a)) 1 = sym (Lemma1 {a} w)
  Lemma (x ≔ a) {σ} {suc (suc f)} (step assign (step () rest)) w
--  Lemma (SKIP ⋯ Q) {σ} {suc f} {finiteComp = ineq} (step seqskip rest) w = Lemma Q {finiteComp = ineq} rest w
  Lemma (P ⋯ Q) {σ} {suc f} semhl w with P ≟ⁱ SKIP
  Lemma (P ⋯ Q) {σ} {suc f} (step seqskip rest) w | yes refl = Lemma Q rest w
  Lemma (P ⋯ Q) {σ} {suc f} (step (seqstep ()) rest) w | yes refl
  ... | no ¬p with ifEnough P Q (suc f) σ
  ... | right (σ' ~ f' ∣ Psem) = Lemma Q (splitseqHL' P Q (suc f) Psem semhl) {!!}
  Lemma (P ⋯ Q) {σ} {suc f} semhl w | no ¬p | left  (σ' ∣ fuelLow) with sym (seqlem2 fuelLow semhl)
  ... | z rewrite z = Lemma P fuelLow {!!}

{-with makeHLstp P {σ} {f} ¬p
  Lemma (P ⋯ Q) {σ} {suc f} (step (seqskip) rest) w | no ¬p | pr ∣ sem = ⊥-elim (¬p refl)
  Lemma (P ⋯ Q) {σ} {suc f} (step (seqstep one) rest) w | no ¬p | pr ∣ sem with detstepHLI one sem | detstepHLσ one sem
  ... | z | z' rewrite z | z' = {!!}-}
  Lemma (IF b THEN P ELSE Q) {σ} {suc f} (step (iftrue prf) rest) w with inspect (bexe b σ)
  ... | false with≡ y rewrite y = ⊥-elim (bool⊥ prf)
  ... | true with≡ _ = Lemma P rest {!!}
  Lemma (IF b THEN P ELSE Q) {σ} {suc f} (step (iffalse prf) rest) w with inspect (bexe b σ)
  ... | true with≡ y rewrite prf = ⊥-elim (bool⊥ y)
  ... | false with≡ _ rewrite prf = Lemma Q rest {!!}
  Lemma (WHILE b DO c) {σ} {suc f}_ _ with inspect (bexe b σ)
  Lemma (WHILE b DO c) {f = suc f}  (step (whiletrue prf)  rest)  w | true with≡ _ rewrite prf = {!!}-- Lemma (c ⋯ (WHILE b DO c))  rest (Lemma5 rest w)
  Lemma (WHILE b DO c) {σ} {suc f} (step (whilefalse prf) done)  w | false with≡ _ rewrite prf with Lemma2 b (compile c & JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []) {0} {$} {σ} prf
  ... | z rewrite size`&+ {compile c} {JMP (neg (+ (size` (bcomp b false (+ (size` (compile c) ℕ+ 1))) ℕ+ size` (compile c) ℕ+ 1))) :: []} = sym (deterministic w z)
  Lemma (WHILE b DO c) {σ} {suc f} (step (whilefalse prf) (step (empty x) rest)) w | false with≡ _ = ⊥-elim (x refl)
  Lemma (WHILE b DO c) {σ} {suc f} (step (whiletrue prf) rest)  w | false with≡ x rewrite x = ⊥-elim (bool⊥ prf)
  Lemma (WHILE b DO c) {σ} {suc f} (step (whilefalse prf) rest)  w | true with≡ x rewrite x = ⊥-elim (bool⊥' prf)

{-  
  Lemma' : ∀ I f σ  → (semLL : ∃[ x ] (compile I ⊢⟦ config σ $ (+ 0) , fuelLL I f (Σ.snd (makeHL I {σ} {f})) ⟧⇒*⟦ config (l x) $ (+ (r x)) , (r (Σ.fst (makeHL I {σ} {f}))) ⟧)) → l (Σ.fst (makeHL I {σ} {f})) ≡ l (Σ.fst semLL)
  Lemma' = {!!}
  
  Lemma' I 0 σ (_ , _ ∣ _) (x , y ∣ some () b)
  Lemma' .SKIP 0 σ (.σ , .0 ∣ done) (.σ , .0 ∣ none) = refl
  Lemma' I 0 σ (.σ , .0 ∣ step (empty _) done) (.σ , .0 ∣ none) = refl
  Lemma' I 0 σ (x , .0 ∣ step (empty _) (step (empty y) z)) (.σ , .0 ∣ none) = ⊥-elim (y refl)
  Lemma' SKIP (suc f) σ (.σ , .(suc f) ∣ done) (.σ , .0 ∣ none) = refl
  Lemma' SKIP (suc f) σ (.σ , .(suc f) ∣ done) (_ , _ ∣ some (⊢LOADI ()) _)
  Lemma' SKIP (suc f) σ (.σ , .(suc f) ∣ done) (_ , _ ∣ some (⊢LOAD ()) _)
  Lemma' SKIP (suc f) σ (.σ , .(suc f) ∣ done) (_ , _ ∣ some (⊢JMP ()) _) 
  Lemma' SKIP                  (suc f) σ (a , b ∣ step () _)
  Lemma' (x ≔ a) (suc f) σ (.((x ≔ aexe a σ) ∷ σ) , .f ∣ step assign done) (x' , y ∣ semhl) rewrite fuelSKIP f {σ = (x ≔ aexe a σ) ∷ σ} {rest = done} = deterministic' semhl (Lemma1''&Store {a})
  Lemma' (x ≔ x₁) (suc .0) σ (a , f' ∣ step assign (step (empty x₂) semhl)) sem2 = ⊥-elim (x₂ refl)
  Lemma' (I ⋯ I₁)              (suc f) σ sem1 sem2 = {!!}
  Lemma' (IF x THEN I ELSE I₁) (suc f) σ sem1 sem2 = {!!}
  Lemma' (WHILE x DO I)        (suc f) σ sem1 sem2 = {!!}
-}
