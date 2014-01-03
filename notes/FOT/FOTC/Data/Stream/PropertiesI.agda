------------------------------------------------------------------------------
-- Stream properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream.PropertiesI using ( Stream-in )
open import FOTC.Data.Stream.Type

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros

zeros-Stream : Stream zeros
zeros-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ zeros

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h Axs = zero , zeros , trans Axs zeros-eq , refl

-- ++-Stream with a diferent type.
++-Stream : ∀ {xs ys} → Stream xs → Stream ys → Stream (xs ++ ys)
++-Stream {xs} {ys} Sxs Sys with Stream-unf Sxs
... | x' , xs' , prf , Sxs' = subst Stream prf₁ prf₂
  where
  prf₁ : x' ∷ (xs' ++ ys) ≡ xs ++ ys
  prf₁ = trans (sym (++-∷ x' xs' ys)) (++-leftCong (sym prf))

  -- TODO (15 December 2013): Why the termination checker accepts the
  -- recursive called ++-Stream_Sxs'_Sys?
  prf₂ : Stream (x' ∷ xs' ++ ys)
  prf₂ = Stream-in (x' , xs' ++ ys , refl , ++-Stream Sxs' Sys)
