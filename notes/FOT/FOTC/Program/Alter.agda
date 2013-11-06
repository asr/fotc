------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Alter where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
alter : D
alter = true ∷ false ∷ alter

alter-Stream : Stream (alter)
alter-Stream = Stream-coind A h₁ h₂
  where
  A : D → Set
  A xs = xs ≡ xs

  h₁ : A alter → ∃[ x' ] ∃[ xs' ] alter ≡ x' ∷ xs' ∧ A xs'
  h₁ _ = true , (false ∷ alter) , refl , refl

  h₂ : A alter
  h₂ = refl
