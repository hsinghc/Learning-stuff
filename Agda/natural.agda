module natural where

  open import boolean 

  data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero + m = m
  suc n + m = suc (n + m)

  _*_ : Nat -> Nat -> Nat
  zero * m = zero
  (suc n) * m = m + (n * m)

  identity : (A : Set) -> A -> A
  identity A x = x

  id : {A : Set} -> A -> A
  id x = x


  _<_ :  Nat -> Nat -> Bool
  _  < zero = false
  zero < suc n = true
  suc m < suc n = m < n

  data Fin′ : Nat → Set where
    zero : (n : _) → Fin′ (suc n)   -- ℕ is inferred
    suc  : (n : _) → Fin′ n → Fin′ (suc n)   -- ℕ is inferred

  x : Fin′ (suc (suc (suc zero)))
  x = suc (suc (suc zero)) (zero (suc zero))

--  Proof₁ : {n m : Nat} -> identity Nat -> ( n + m )
 -- Proof₁ = zero
 -- data ⊥ : Set where

  record ⊤ : Set where
 -- data ⊥ : Set where

  data  _≤_ : Nat → Nat → Set where
    z≤n : {n : Nat} → zero  ≤ n
    s≤s : {m : Nat} → {n : Nat} →   m ≤ n  →  suc m ≤ suc n

  0≤1 : (suc zero) ≤ (suc (suc (suc zero)))
  0≤1 = s≤s z≤n

  
  7≰3 : (suc (suc (suc (suc zero)))) ≤ (suc (suc (suc zero))) → ⊥
  7≰3 (s≤s (s≤s (s≤s ())))
  
  data _≡_ {A : Set} (x : A) : A → Set  where
     refl : x ≡ x

  Proof₄ : Nat
  Proof₄ = zero

  refl'  : ∀ {A} (a : A) → a ≡ a
  refl' a = refl

  sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
  cong f refl = refl

  even : Nat → Set
  even zero = ⊤
  even (suc zero) = ⊥
  even (suc (suc n)) = even n

  div2e : (n : Nat) → even n → Nat -- Note, we have to give a name `n` to the first argument here
  div2e zero p = zero
  div2e (suc zero) ()
  div2e (suc (suc y)) p = suc (div2e y p)

 -- Proof₂ : Nat
 -- Proof₂ = div2e (suc (suc (suc zero))) {!!}

  data Square (A : Set) : Set where
    zeroM :            A  → Square A   -- 2^0 rows
    sucM  : Square ( A) → Square A  

