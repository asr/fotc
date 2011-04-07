------------------------------------------------------------------------------
-- Testing the removal of the quantification
------------------------------------------------------------------------------

-- See also Test.Succeed.NonConjectures.DefinitionInsideWhereClause

module Test.Succeed.NonConjectures.EraseQuantification where

postulate
  D    : Set
  _≡_  : D → D → Set
  succ : D → D

module EraseQuantificationOnProofs where

  -- The data constructors sN₁ and sN₂ must have the same translation,
  -- i.e. we must erase the quantification on the variable Nn : N n.
  -- The translation of sN₂ must be '∀ x. N(x) → N(succ(x))

  data N : D → Set where
    -- zN : N zero
    sN₁ : ∀ {n} → N n → N (succ n)
    sN₂ : ∀ {n} → (Nn : N n) → N (succ n)
  {-# ATP axiom sN₁ #-}
  {-# ATP axiom sN₂ #-}

-- module EraseQuantificationOverFunctionsAndPiTerm

-- -- Possible test

-- data A : Set where
--   a : A

-- foo : {e : D } → (N e → D) → A → e ≡ e
-- foo {e} fn a = prf
--   where
--   postulate prf : e ≡ e
--   {-# ATP prove prf #-}

-- bar : {e : D } → ((d : D) → N d → D) → A → e ≡ e
-- bar {e} fn a = prf
--   where
--   postulate prf : e ≡ e
--   {-# ATP prove prf #-}
