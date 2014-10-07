------------------------------------------------------------------------------
-- Stream properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Colist.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream.PropertiesI
open import FOTC.Data.Stream.Type

------------------------------------------------------------------------------

{-# TERMINATING #-}
++-Stream : ∀ {xs ys} → Colist xs → Stream ys → Stream (xs ++ ys)
++-Stream {xs} {ys} CLxs Sys with Colist-out CLxs
... | inj₁ prf = subst Stream (sym prf₁) Sys
 where
 prf₁ : xs ++ ys ≡ ys
 prf₁ = trans (++-leftCong prf) (++-[] ys)

... | inj₂ (x' , xs' , prf , CLxs') = subst Stream (sym prf₁) prf₂
   where
   prf₁ : xs ++ ys ≡ x' ∷ (xs' ++ ys)
   prf₁ = trans (++-leftCong prf) (++-∷ x' xs' ys)

   prf₂ : Stream (x' ∷ xs' ++ ys)
   prf₂ = Stream-in (x' , (xs' ++ ys) , refl , ++-Stream CLxs' Sys)

-- ++-Stream with a diferent type.
{-# TERMINATING #-}
++-Stream' : ∀ {xs ys} → Stream xs → Stream ys → Stream (xs ++ ys)
++-Stream' {xs} {ys} Sxs Sys with Stream-out Sxs
... | x' , xs' , prf , Sxs' = subst Stream prf₁ prf₂
  where
  prf₁ : x' ∷ (xs' ++ ys) ≡ xs ++ ys
  prf₁ = trans (sym (++-∷ x' xs' ys)) (++-leftCong (sym prf))

  prf₂ : Stream (x' ∷ xs' ++ ys)
  prf₂ = Stream-in (x' , xs' ++ ys , refl , ++-Stream' Sxs' Sys)
