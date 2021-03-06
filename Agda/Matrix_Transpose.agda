module Matrix_Transpose where
{-
  open import Data.Nat
  open import Data.Vec

  Matrix : (A : Set) → ℕ → ℕ → Set
  Matrix A m n = Vec (Vec A m) n
  
  transpose : ∀ {A m n} → Matrix A m n → Matrix A n m
  transpose [] = replicate []
  transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)
  
  a = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []
  b = transpose a
-}

  open import natural
  open import boolean

 
  data Vec (A : Set) : Nat -> Set where
    [] : Vec A zero
    _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

  vec : (n : Nat){A : Set} -> A -> Vec A n
  vec zero x = []
  vec (suc n) x = x :: vec n x

  infixl 90 _$_

  _$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
  [] $ [] = []
  (f :: fs) $ (x :: xs) = (f x) :: (fs $ xs)

--  _ fillto _ : {n m k : Nat}{A B C : Set} -> Vec A n -> Vec (Vec A m)  n -> Vec (Vec A k) n 
--  [] fillto []  = ks
--  (f :: fs) fillto (x :: xs) = (f :: x) :: (fs fillto xs)

  --pop  : {n : Nat}{A : Set} -> Vec A (suc n) -> A
  --pop x :: xs  =  x

  pop : {A : Set}{n : Nat}  ->  Vec A (suc n) -> A
  pop (x :: xs) = x

  length : {A : Set}{n : Nat} -> Vec A n -> Nat
  length [] = zero
  length (x :: xs) = suc (length xs)

  data False1 : Set where
  record True1 : Set where


  Proof₁₀ : True1
  Proof₁₀ = record { }

  _less_ :  Nat -> Nat -> Set
  _  less zero = False1
  zero less suc n = True1
  suc m less suc n = m less n
  
{-  lookup : {A : Set}{ n : Nat} -> (p : Nat)  -> Vec A n ->  A
  lookup p xs with (p less (length xs))
  lookup zero (x :: x1) | Truth = x
  lookup (suc r) (x :: x1) | Truth = lookup r x1
  --lookup  _ (x :: [] ) | _ = x
  lookup _ [] | False1 = lookup zero []   
  --lookup p [] with True1
-- lookup  k [] with ( ((suc zero) < zero) ⋍ true )
 -- lookup  k [] | ()
-}

  Matrix : Set -> Nat -> Nat -> Set
--  Matrix A zero zero = []
--  Matrix A n zero = []
--  Matrix A m zero = []
  Matrix A n m = Vec (Vec A n) m



  fillto  : ∀ {n m } {A : Set} -> Vec A n -> Matrix A m n -> Matrix A (suc m) n
  fillto [] [] = []
  fillto (f :: fs)  (x :: xs) = (f :: x) :: (fillto fs xs)
--Vec is vertical

  --transpose zero n m mat _ = Vec A zero
  --transpose (suc zero) n m mat z = ((vec m (lookup zero) $ mat))
{-  transpose row n m mat with ( zero < row )
  transpose (suc p) n m mat | true =  ((vec m ( lookup  p )) $ mat)  :: (transpose p n m mat ) 
  transpose row n m mat | false = [] 
  transpose zero n m mat = []
  -}
  transpose :   ∀ {A n}  → (m : Nat) -> Matrix A m n → Matrix A n m
  transpose m [] = vec m []
  transpose m (x :: xs) =  fillto x  (transpose m xs)

  Proof₁ : Matrix Nat (suc (suc (suc zero))) (suc (suc zero))
  Proof₁ = transpose (suc (suc zero)) (((suc zero) :: (zero :: [])) ::
                                         ((zero :: (zero :: [])) :: ((zero :: (zero :: [])) :: [])))
-- Proof₁ = (zero :: (zero :: (zero :: []))) ::
           --  ((zero :: (zero :: (zero :: []))) :: [])
--  Proof₁ = transpose (suc (suc zero)) ((zero :: (zero :: [])) ::
--                                         ((zero :: (zero :: [])) :: ((zero :: (zero :: [])) :: [])))
-- Proof₁ = transpose (suc (suc zero)) ((zero :: (zero :: [])) :: ((zero :: (zero :: [])) :: []))
-- Proof₁ = transpose (suc (suc zero)) ((zero :: (zero :: [])) :: ((zero :: (zero :: [])) :: []))
-- Proof₁ = transpose (suc (suc zero)) ( ( zero ::( zero :: [] )) :: (( zero ::( zero :: []) ) :: [] )) 
-- Proof₁ = ?
-- Proof₁ :  (( zero :: (zero :: []) ) :: ((zero :: (zero :: []) ) :: ([] :: [] :: []) ))
-- Proof₁ =  transpose (suc (suc zero)) (( zero :: (zero :: []) ) :: ((zero :: (zero :: []) ) :: [] )) 
-- lookup : {A : Set}{ n : Nat} -> (p : Nat)  -> Vec A n ->  A
-- lookup p xs with (p less (length xs))

