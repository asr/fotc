------------------------------------------------------------------------------
-- Testing the removal of the quantification
------------------------------------------------------------------------------

module Test.Succeed.OnlyAxioms.EraseQuantification where

postulate
  D    : Set
  _≡_  : D → D → Set
  succ : D → D

module EraseQuantificationOnSet where

  postulate a : D

  -- The translation must erase the quantification on Set (i.e. {A : Set}),
  -- the translation must be 'a = a'.
  postulate foo : {A : Set} → a ≡ a
  {-# ATP axiom foo #-}

module EraseQuantificationOnProofs where

  -- The data constructors sN₁ and sN₂ must have the same translation,
  -- i.e. we must erase the quantification of the variable Nn on N n.
  -- The translation of sN₂ must be '∀ x. n(x) → n(succ(x))

  data N : D → Set where
    -- zN : N zero
    sN₁ : {n : D} →  N n → N (succ n)
    sN₂ : {n : D} → (Nn : N n) → N (succ n)
  {-# ATP hint sN₂ #-}

  -- We need to remove the quantification over proofs inside a where
  -- clause. The translation of P must be '∀ x. ∀ y. p(x, y) ↔ y = x',
  -- i.e. we must erase the quantification on N n.
  foo : (n : D) → N n → Set
  foo n Nn = P n
    where
      P : D → Set
      P m = m ≡ n
      {-# ATP definition P #-}

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
