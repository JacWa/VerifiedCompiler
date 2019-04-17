module Lang.Expr where

  -- Data.* files are imported from agda-stdlib
  open import Function using (_∘_)
  open import Agda.Builtin.Nat using (_<_)
  open import Data.Nat using (ℕ; suc) renaming (_+_ to _ℕ+_; _≟_ to ℕeq?)
  open import Agda.Builtin.Equality
  open import Data.String renaming (_≟_ to streq?)
  open import Data.Bool renaming (_≟_ to booleq?)
  open import Data.Empty
  open import Base.DataStructures  
  open import Relation.Binary.Core
  open import Relation.Binary.PropositionalEquality using (cong; subst)
  open import Relation.Nullary
  
----------------------------
-- Expression definitions --
----------------------------

  -- Arithmetic Expressions
  data AExp : Set where  
    NAT   : ℕ → AExp
    VAR   : String → AExp
    _+_   : AExp → AExp → AExp

  -- Boolean Expressions
  data BExp : Set where
    BOOL    : Bool → BExp
    NOT     : BExp → BExp
    _AND_   : BExp → BExp → BExp
    _LT_    : AExp → AExp → BExp

  -- Instructions
  infixl 20 _⋯_
  data IExp : Set where
    SKIP          : IExp
    _≔_          : String → AExp → IExp
    _⋯_          : IExp → IExp → IExp
    IF_THEN_ELSE_ : BExp → IExp → IExp → IExp
    WHILE_DO_     : BExp → IExp → IExp

  -- Execute arithmetic expressions
  aexe : AExp → State → ℕ
  aexe (NAT val)  _     = val
  aexe (VAR name) state = get-var name state 
  aexe (x + y)    state = (aexe x state) ℕ+ (aexe y state)

  -- Execute boolean expressions
  bexe : BExp → State → Bool
  bexe (BOOL b)  _     = b
  bexe (NOT x)   state = not (bexe x state)
  bexe (x AND y) state = (bexe x state) ∧ (bexe y state)
  bexe (m LT n)  state = (aexe m state) < (aexe n state)

  aeq?-1 : ∀ {n n'} → NAT n ≡ NAT n' → n ≡ n'
  aeq?-1 refl = refl

  aeq?-2 : ∀ {n n'} → VAR n ≡ VAR n' → n ≡ n'
  aeq?-2 refl = refl
  
  aeq?-3-l : ∀ {n n' n'' n'''} → n + n'' ≡ n' + n''' → n ≡ n'
  aeq?-3-l refl = refl
  
  aeq?-3-r : ∀ {n n' n'' n'''} → n + n'' ≡ n' + n''' → n'' ≡ n'''
  aeq?-3-r refl = refl

  aeq? : Decidable {A = AExp} _≡_
  aeq? (NAT n) (NAT n') with ℕeq? n n'
  ... | yes refl = yes refl
  ... | no ¬p = no (¬p ∘ aeq?-1)
  aeq? (NAT x) (VAR x') = no (λ ())
  aeq? (NAT x) (a + a') = no (λ ())
  aeq? (VAR x) (NAT x') = no (λ ())
  aeq? (VAR x) (VAR x') with streq? x x'
  ... | yes refl = yes refl
  ... | no ¬p = no (¬p ∘ aeq?-2)
  aeq? (VAR x) (a' + a'') = no (λ ())
  aeq? (a + a') (NAT x) = no (λ ())
  aeq? (a + a') (VAR x) = no (λ ())
  aeq? (a + a'') (a' + a''') with aeq? a a' | aeq? a'' a'''
  ... | yes refl | yes refl = yes refl
  ... | no prf  | _ = no (prf ∘ aeq?-3-l)
  ... | _ | no prf  = no (prf ∘ aeq?-3-r)

  beq?-bool : ∀ {b b'} → BOOL b ≡ BOOL b' → b ≡ b'
  beq?-bool refl = refl

  beq?-not : ∀ {b b'} → NOT b ≡ NOT b' → b ≡ b'
  beq?-not refl = refl

  beq?-AND-l : ∀ {a a' b b'} → a AND b ≡ a' AND b' → a ≡ a'
  beq?-AND-l refl = refl
  
  beq?-AND-r : ∀ {a a' b b'} → a AND b ≡ a' AND b' → b ≡ b'
  beq?-AND-r refl = refl

  beq?-LT-l : ∀ {a a' b b'} → a LT b ≡ a' LT b' → a ≡ a'
  beq?-LT-l refl = refl
  
  beq?-LT-r : ∀ {a a' b b'} → a LT b ≡ a' LT b' → b ≡ b'
  beq?-LT-r refl = refl

  beq? : Decidable {A = BExp} _≡_
  beq? (BOOL x) (BOOL x₁) with booleq? x x₁
  ... | yes refl = yes refl
  ... | no ¬p = no (¬p ∘ beq?-bool)
  beq? (BOOL x) (NOT b') = no (λ ())
  beq? (BOOL x) (b' AND b'') = no (λ ())
  beq? (BOOL x) (x₁ LT x₂) = no (λ ())
  beq? (NOT b) (BOOL x) = no (λ ())
  beq? (NOT b) (NOT b') with beq? b b'
  ... | yes refl = yes refl
  ... | no ¬p = no (¬p ∘ beq?-not)
  beq? (NOT b) (b' AND b'') = no (λ ())
  beq? (NOT b) (x LT x₁) = no (λ ())
  beq? (b AND b₁) (BOOL x) = no (λ ())
  beq? (b AND b₁) (NOT b') = no (λ ())
  beq? (b AND b₁) (b' AND b'') with beq? b b' | beq? b₁ b''
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no (¬p ∘ beq?-AND-l)
  ... | _ | no ¬p = no (¬p ∘ beq?-AND-r)
  beq? (b AND b₁) (x LT x₁) = no (λ ())
  beq? (x LT x₁) (BOOL x₂) = no (λ ())
  beq? (x LT x₁) (NOT b') = no (λ ())
  beq? (x LT x₁) (b' AND b'') = no (λ ())
  beq? (x LT x') (x'' LT x''') with aeq? x x'' | aeq? x' x'''
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no (¬p ∘ beq?-LT-l)
  ... | _ | no ¬p = no (¬p ∘ beq?-LT-r)

  ieq-≔-str : {x x' : String}{a a' : AExp} → _≡_ {A = IExp} (x ≔ a) (x' ≔ a') → x ≡ x'
  ieq-≔-str refl = refl

  ieq-≔-axp : {x x' : String}{a a' : AExp} → _≡_ {A = IExp} (x ≔ a) (x' ≔ a') → a ≡ a'
  ieq-≔-axp refl = refl

  ieq-⋯-l : ∀ {i i' i'' i'''} → i ⋯ i' ≡ i'' ⋯ i''' → i ≡ i''
  ieq-⋯-l refl = refl

  ieq-⋯-r : ∀ {i i' i'' i'''} → i ⋯ i' ≡ i'' ⋯ i''' → i' ≡ i'''
  ieq-⋯-r refl = refl

  ieq-if-b : ∀ {b b' this this' that that'} → IF b THEN this ELSE that ≡ IF b' THEN this' ELSE that' → b ≡ b'
  ieq-if-b refl = refl

  ieq-if-this : ∀ {b b' this this' that that'} → IF b THEN this ELSE that ≡ IF b' THEN this' ELSE that' → this ≡ this'
  ieq-if-this refl = refl

  ieq-if-that : ∀ {b b' this this' that that'} → IF b THEN this ELSE that ≡ IF b' THEN this' ELSE that' → that ≡ that'
  ieq-if-that refl = refl

  ieq-whl-b : ∀ {b b' c c'} → WHILE b DO c ≡ WHILE b' DO c' → b ≡ b'
  ieq-whl-b refl = refl

  ieq-whl-c : ∀ {b b' c c'} → WHILE b DO c ≡ WHILE b' DO c' → c ≡ c'
  ieq-whl-c refl = refl

  _≟_ :  Decidable {A = IExp} _≡_
  SKIP ≟ SKIP = yes refl
  SKIP ≟ (x ≔ a) = no λ ()
  SKIP ≟ (i' ⋯ i'') = no (λ ())
  SKIP ≟ (IF x THEN i' ELSE i'') = no (λ ())
  SKIP ≟ (WHILE x DO i') = no (λ ())
  (x ≔ a) ≟ SKIP = no (λ ())
  (x ≔ a) ≟ (x' ≔ a') with streq? x x' | aeq? a a'
  ... | yes refl | yes refl = yes refl
  ... | no prf | _ = no (prf ∘ ieq-≔-str)
  ... | _ | no prf = no (prf ∘ ieq-≔-axp)
  (x ≔ a) ≟ (i' ⋯ i'') = no (λ ())
  (x ≔ a) ≟ (IF x₂ THEN i' ELSE i'') = no (λ ())
  (x ≔ a) ≟ (WHILE x₂ DO i') = no (λ ())
  (i ⋯ i') ≟ SKIP = no (λ ())
  (i ⋯ i') ≟ (x ≔ a) = no (λ ())
  (i ⋯ i') ≟ (i'' ⋯ i''') with i ≟ i'' | i' ≟ i'''
  ... | yes refl | yes refl = yes refl
  ... | no prf | _ = no (prf ∘ ieq-⋯-l)
  ... | _ | no prf = no (prf ∘ ieq-⋯-r)
  (i ⋯ i') ≟ (IF x THEN i'' ELSE i''') = no (λ ())
  (i ⋯ i') ≟ (WHILE x DO i'') = no (λ ())
  (IF x THEN i ELSE i₁) ≟ SKIP = no (λ ())
  (IF x THEN i ELSE i₁) ≟ (x₁ ≔ x₂) = no (λ ())
  (IF x THEN i ELSE i₁) ≟ (i' ⋯ i'') = no (λ ())
  (IF x THEN i ELSE i'') ≟ (IF x' THEN i' ELSE i''') with beq? x x' | i ≟ i' | i'' ≟ i'''
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no (¬p ∘ ieq-if-b)
  ... | _ | no ¬p | _ = no (¬p ∘ ieq-if-this)
  ... | _ | _ | no ¬p = no (¬p ∘ ieq-if-that)
  (IF x THEN i ELSE i₁) ≟ (WHILE x₁ DO i') = no (λ ())
  (WHILE x DO i) ≟ SKIP = no (λ ())
  (WHILE x DO i) ≟ (x₁ ≔ x₂) = no (λ ())
  (WHILE x DO i) ≟ (i' ⋯ i'') = no (λ ())
  (WHILE x DO i) ≟ (IF x₁ THEN i' ELSE i'') = no (λ ())
  (WHILE x DO i) ≟ (WHILE x' DO i') with beq? x x' | i ≟ i'
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no (¬p ∘ ieq-whl-b)
  ... | _ | no ¬p = no (¬p ∘ ieq-whl-c)
