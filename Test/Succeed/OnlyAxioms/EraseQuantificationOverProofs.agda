------------------------------------------------------------------------------
-- Testing the removal of the quantification over proofs of formulas
------------------------------------------------------------------------------

module Test.Succeed.OnlyAxioms.EraseQuantificationOverProofs where

postulate
  D    : Set
  succ : D → D
  _≡_  : D → D → Set

data N : D → Set where
  -- zN : N zero
  sN₁ : {n : D} →  N n → N (succ n)
  sN₂ : {n : D} → (Nn : N n) → N (succ n)

-- The data constructors sN₁ and sN₂ must have the same translation,
-- i.e. we must erase the quantification of the variable Nn on N n.

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


-- We need to remove the quantification over proofs inside a where
-- clause. The translation of P must be '∀ x. ∀ y. p(x, y) ↔ y = x',
-- i.e. we must erase the quantification on N n.
foo : (n : D) → N n → Set
foo n Nn = P n
  where
    P : D → Set
    P m = m ≡ n
    {-# ATP definition P #-}
