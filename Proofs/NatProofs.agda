module Proofs.NatProofs where

    open import Data.Nat.Base
    open import Relation.Nullary.Decidable
    open import Agda.Builtin.Equality
    open import Proofs.Basic

    +1≡suc : (n : ℕ) → n + 1 ≡ suc n
    +1≡suc 0 = refl
    +1≡suc (suc n) rewrite +1≡suc n = refl

    suc≡+1 : (n : ℕ) → suc n ≡ n + 1
    suc≡+1 n = sym (+1≡suc n)

    *1 : (n : ℕ) → n * 1 ≡ n
    *1 0 = refl
    *1 (suc x) rewrite *1 x = refl

    +swap : {a b : ℕ} → suc (a + b) ≡ (a + suc b)
    +swap {0} {b} = refl
    +swap {suc a} {b} with (a + suc b) | (+swap {a} {b})
    ... | .(suc (a + b)) | refl = refl

    +0 : (a : ℕ) → (a + 0) ≡ a
    +0 0 = refl
    +0 (suc a) rewrite +0 a = refl

    +comm : (n m : ℕ) → (n + m) ≡ (m + n)
    +comm 0 m rewrite +0 m = refl
    +comm (suc n) m with (n + m) | +comm n m
    ... | .(m + n) | refl = +swap {m} {n}
    
    sucswap : ∀ a b → a + suc b ≡ b + suc a
    sucswap 0 b rewrite +comm b 1 = refl
    sucswap (suc a) b rewrite +comm b (suc (suc a)) | +comm a (suc b) | +comm a b = refl


    +assoc : (x y z : ℕ) → (x + (y + z)) ≡ ((x + y) + z)
    +assoc 0 y z = refl
    +assoc (suc x) y z rewrite +assoc x y z = refl

    +oswap : (x y z : ℕ) → (x + (y + z)) ≡ (y + (x + z))
    +oswap x y z rewrite +assoc x y z | +assoc y x z | +comm x y = refl

    +3free4 : (a b c d : ℕ) → (a + (b + (c + d))) ≡ c + (a + (b + d))
    +3free4 a b c d rewrite +oswap b c d | +oswap a c (b + d) = refl

    *0 : (x : ℕ) → (x * 0) ≡ 0
    *0 0 = refl
    *0 (suc x) rewrite *0 x = refl

    +*aab : (x y : ℕ) → y + y * x ≡ y * suc x
    +*aab x 0 = refl
    +*aab x (suc n) with (n * suc x) | +*aab x n
    ... | .(n + n * x) | refl rewrite +assoc x n (n * x) | +assoc n x (n * x) | +comm n x = refl
    
    *comm : (x y : ℕ) → (x * y) ≡ (y * x)
    *comm 0 y rewrite *0 y = refl
    *comm (suc x) y rewrite *comm x y = +*aab x y

    +*aba : (x y : ℕ) → y + x * y ≡ y * suc x
    +*aba x 0 rewrite *comm x 0 = refl
    +*aba x (suc y) with (x * (suc y)) | *comm x (suc y) | (y * (suc x)) | *comm y (suc x)
    ... | .((suc y) * x) | refl | .((suc x) * y) | refl rewrite +assoc y x (y * x) | +assoc x y (x * y) | +comm x y | *comm x y = refl

    +*dist : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
    +*dist 0 _ _ = refl
    +*dist (suc x) y z rewrite +*dist x y z | +assoc z (x * z) (y * z) = refl
    
    *assoc : (l m n : ℕ) → (l * m) * n ≡ l * (m * n)
    *assoc 0 _ _ = refl
    *assoc (suc l) m n rewrite *assoc l m n | +*dist m (l * m) n | *assoc l m n = refl


    -- Properties of exponents

    -- This is built-in to the definition of _^_, but can be useful with rewrite to make the goal appear in a different form.
    ^0 : (n : ℕ) → n ^ 0 ≡ 1
    ^0 n = refl
    
    ^* : (n x y : ℕ) → n ^ x * n ^ y ≡ n ^ (x + y)
    ^* n 0 y rewrite +0 (n ^ y) = refl
    ^* n (suc x) y rewrite *assoc n (n ^ x) (n ^ y) | ^* n x y = refl

    ^^ : (n x y : ℕ) → (n ^ x) ^ y ≡ n ^ (x * y)
    ^^ n x 0 rewrite *0 x = refl
    ^^ n x (suc y) rewrite *comm x (suc y) | ^^ n x y | ^* n x (x * y) | *comm x y = refl

    *^ : (x y n : ℕ) → (x * y) ^ n ≡ x ^ n * y ^ n
    *^ x y 0 = refl
    *^ x y (suc n) rewrite *^ x y n | *assoc x y (x ^ n * y ^ n) | *comm y (x ^ n * y ^ n) | *comm y (y ^ n) | *assoc x (x ^ n) ((y ^ n) * y) | *assoc (x ^ n) (y ^ n) y = refl

    

    data _=<_ : ℕ → ℕ → Set where
        zero : {m : ℕ} → 0 =< m
        sucr : {m n : ℕ} → (m =< n) → (m =< (suc n))
        sucb : {m n : ℕ} → (m =< n) → ((suc m) =< (suc n))


    =<+r : ∀ {x y}(z : ℕ) → x =< y → x =< (z + y)
    =<+r 0 p = p
    =<+r (suc n) p = sucr (=<+r n p)

    =<*r : ∀ {x y}(z : ℕ){f : False (z ≟ 0)} → x =< y → x =< (z * y)
    =<*r 0 {}
    =<*r {y = y} 1 p rewrite *comm 1 y | *1 y = p
    =<*r {y = y} (suc (suc n)) p = =<+r y (=<*r (suc n) p)

    =<^r :  ∀ {x y}(z : ℕ){f : False (z ≟ 0)} → x =< y → x =< (y ^ z)
    =<^r 0 {}
    =<^r {y = y} 1 p rewrite *comm y (y ^ 0) | +0 y = p
    =<^r {y = 0} (suc (suc n)) p rewrite *0 n = p
    =<^r {y = suc y} (suc (suc n)) p = =<*r (suc y) (=<^r (suc n) p)

    test : (n : ℕ) → n + 2 ≡ (suc n) + 1
    test 0 = refl
    test (suc x) rewrite test x = refl
