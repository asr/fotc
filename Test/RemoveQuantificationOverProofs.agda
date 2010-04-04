------------------------------------------------------------------------------
-- Testing the removal of the quantification over proofs of formulas
------------------------------------------------------------------------------

module Test.RemoveQuantificationOverProofs where

postulate
  D      : Set
  zero   : D
  succ   : D → D
  pred   : D → D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN₁ : {n : D} →  N n → N (succ n)
  sN₂ : {n : D} → (Nn : N n) → N (succ n)

-- The data constructors sN₁ and sN₂ must have the same translation,
-- i.e. we must remove the quantification of the variable Nn on N n.

{-# ATP hint sN₁ #-}
{-# ATP hint sN₂ #-}

-- The Agda internal type of sN₁
{-
El (Type (Lit (LitLevel  0)))
   (Pi {El (Type (Lit (LitLevel  0)))
           (Def Test.RemoveQuantificationOverProofs.D [])}
       (Abs "n" El (Type (Lit (LitLevel  0)))
                   (Fun (El (Type (Lit (LitLevel  0)))
                            (Def Test.RemoveQuantificationOverProofs.N [(Var 0 [])]))
                        (El (Type (Lit (LitLevel  0)))
                            (Def Test.RemoveQuantificationOverProofs.N
                                 [(Def Test.RemoveQuantificationOverProofs.succ [(Var 0 [])])]
                            )
                        )
                   )
       )
   )
-}

-- The Agda internal type of sN₂
{-
El (Type (Lit (LitLevel  0)))
   (Pi {El (Type (Lit (LitLevel  0)))
           (Def Test.RemoveQuantificationOverProofs.D [])}
       (Abs "n" El (Type (Lit (LitLevel  0)))
                   (Pi (El (Type (Lit (LitLevel  0)))
                           (Def Test.RemoveQuantificationOverProofs.N [(Var 0 [])]))
                       (Abs "Nn" El (Type (Lit (LitLevel  0)))
                                    (Def Test.RemoveQuantificationOverProofs.N
                                         [(Def Test.RemoveQuantificationOverProofs.succ [(Var 1 [])])]
                                    )
                       )
                   )
       )
   )
-}

-- We test the translation of the data constructors sN₁ and sN₂ with a
-- conjecture that use the data constructor sN.

postulate
  -- A conversion rules for pred.
  cP₂ : (n : D) → pred (succ n) ≡ n
{-# ATP axiom cP₂ #-}

postulate
  pred-N-prf₂₁ : {n : D} → N n → N (pred (succ n))
{-# ATP prove pred-N-prf₂₁ sN₁ #-}

postulate
  pred-N-prf₂₂ : {n : D} → N n → N (pred (succ n))
{-# ATP prove pred-N-prf₂₂ sN₂ #-}
