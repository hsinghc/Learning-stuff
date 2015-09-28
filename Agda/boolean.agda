module boolean where

  data Bool : Set where
    true : Bool
    false : Bool
    indet : Bool
-- data True : Bool where
--  true : True

-- data False : Bool where
--  false : False
  data _True : Bool → Set where
    truth : true True
 
  _⋍_ : Bool → Bool → Set
  true ⋍ true = true True
  false ⋍ false = true True
  true ⋍ false = false True
  false ⋍ true = false True
  indet ⋍ indet = true True
  indet ⋍ false = indet True
  indet ⋍ true = indet True
  false ⋍ indet = indet True
  true ⋍ indet = indet True

  data ⊥ : Set where
  
   -- _∧_ : True → True → True
   -- STEP : (m : True) → (n : True) → obvious True

  ∨ : Bool → Bool → Bool
  ∨ false false = false
  ∨ true _ = true
  ∨ _ true = true
  ∨ indet _ = indet 
  ∨ _ indet = indet

{-p∨q → p/q → q/p-}
  ∨e : Bool → Bool → Bool
  ∨e false _ = false
  ∨e indet _ = indet
  ∨e true false = true
  ∨e true _ = indet
  
  ∧ : Bool → Bool → Bool
  ∧ false false = false
  ∧ true false = false
  ∧ false true = false
  ∧ true true = true
  ∧ indet _ = indet 
  ∧ _ indet = indet

  ∧e : Bool → Bool
  ∧e  true = true
  ∧e  _ = indet

{- p⇒q → q -}
  /→e : Bool  → Bool → Bool
  /→e true true = indet
  /→e true false = false
  /→e false false = true
  /→e false true = false
  /→e indet _ = indet
  /→e _ indet = indet

{- p⇒q → p -}
  /→e2 : Bool  → Bool → Bool
  /→e2 true true = true
  /→e2 _ false = indet
  /→e2 false true = false
  /→e2 indet _ = indet
  /→e2 _ indet = indet

  /→ : Bool → Bool → Bool
  /→ false false = true
  /→ true false = false
  /→ false true = true
  /→ true true = true
  /→ _ indet = indet
  /→ indet true = true
  /→ indet _ = indet

  /→i : Bool → Bool → Bool
  /→i false _ = indet
  /→i true false = false
  /→i true true = true
  /→i true indet = indet
  /→i indet _ = indet
 
  ¬ : Bool → Bool
  ¬ false = true
  ¬ true = false
  ¬ indet = indet
