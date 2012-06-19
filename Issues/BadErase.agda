------------------------------------------------------------------------------
-- The translation is badly erasing the universal quantification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issues.BadErase where

postulate
  _↔_ : Set → Set → Set
  D   : Set
  A   : Set

postulate bad₁ : ((x : D) → A) → A
{-# ATP prove bad₁ #-}

-- Before the patch
--
-- Wed Sep 21 04:50:43 COT 2011  ulfn@chalmers.se
--   * got rid of the Fun constructor in internal syntax (using Pi _ (NoAbs _ _) instead)
--
-- the type of bad₁ was:
--
-- Type: El (Type (Max [])) (Fun r(El (Type (Max [])) (Pi r(El (Type (Max [])) (Def BadErase.D [])) (Abs "x" El (Type (Max [])) (Def BadErase.A [])))) (El (Type (Max [])) (Def BadErase.A [])))
--
--
-- After the above patch the type of bad₁ was:
--
-- Type: El (Type (Max [])) (Pi r(El (Type (Max [])) (Pi r(El (Type (Max [])) (Def BadErase.D [])) (Abs "x" El (Type (Max [])) (Def BadErase.A [])))) (NoAbs "_" El (Type (Max [])) (Def BadErase.A [])))
--
--
-- On 19 June 2012, the type of bad₁ is:
--
-- Type: El {getSort = Type (Max []), unEl = Pi r(El {getSort = Type (Max []), unEl = Pi r(El {getSort = Type (Max []), unEl = Def BadErase.D []}) (NoAbs "x" El {getSort = Type (Max []), unEl = Def BadErase.A []})}) (NoAbs "_" El {getSort = Type (Max []), unEl = Def BadErase.A []})}

postulate bad₂ : A → ((x : D) → A)
{-# ATP prove bad₂ #-}

postulate bad₃ : ((x : D) → A) ↔ A
{-# ATP prove bad₃ #-}
