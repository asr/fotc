------------------------------------------------------------------------------
-- Testing the removal of the quantification on proof terms
------------------------------------------------------------------------------

module Test.Succeed.EraseQuantificationOnProofTerms1 where

-- The data constructors sN₁ and sN₂ must have the same translation,
-- i.e. we must erase the quantification on the variable Nn : N n.
-- The translation of sN₁ and sN₂ must be ∀ x. N(x) → N(succ(x)).

-- The Agda (development version on 21 July 2011) internal types are
-- the followings.

-- For sN₁:

{-
El (Type (Max []))
   (Pi !{El (Type (Max []))
            (Def Test.Succeed.EraseQuantificationOnProofTerms1.D [])}
       (Abs "n" El (Type (Max []))
                   (Fun r(El (Type (Max []))
                             (Def Test.Succeed.EraseQuantificationOnProofTerms1.N [r(Var 0 [])]))
                        (El (Type (Max []))
                            (Def Test.Succeed.EraseQuantificationOnProofTerms1.N [r(Def Test.Succeed.EraseQuantificationOnProofTerms1.succ [r(Var 0 [])])])))))
-}

-- For sN₂:
{-
El (Type (Max []))
   (Pi !{El (Type (Max []))
            (Def Test.Succeed.EraseQuantificationOnProofTerms1.D [])}
       (Abs "n" El (Type (Max []))
               (Pi r(El (Type (Max []))
                        (Def Test.Succeed.EraseQuantificationOnProofTerms1.N [r(Var 0 [])]))
                   (Abs "Nn" El (Type (Max []))
                                (Def Test.Succeed.EraseQuantificationOnProofTerms1.N [r(Def Test.Succeed.EraseQuantificationOnProofTerms1.succ [r(Var 1 [])])])))))
-}

postulate
  D    : Set
  succ : D → D

data N : D → Set where
  -- zN : N zero
  sN₁ : ∀ {n} → N n → N (succ n)
  sN₂ : ∀ {n} → (Nn : N n) → N (succ n)
{-# ATP axiom sN₁ #-}
{-# ATP axiom sN₂ #-}

------------------------------------------------------------------------------
-- We need to have at least one conjecture to generate a TPTP file.
postulate
  _≡_  : D → D → Set
  refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
