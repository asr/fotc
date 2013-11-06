------------------------------------------------------------------------------
-- Properties of the alter list
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Alter.PropertiesATP where

open import FOT.FOTC.Program.Alter.Alter

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

alter-Stream : Stream alter
alter-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs
  {-# ATP definition A #-}

  postulate h : A alter → ∃[ x' ] ∃[ xs' ] alter ≡ x' ∷ xs' ∧ A xs'
  {-# ATP prove h #-}
