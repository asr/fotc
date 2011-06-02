------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC list type)
------------------------------------------------------------------------------

module FOTC.Data.List.PropertiesByInductionATP where

open import FOTC.Base

open import FOTC.Data.List
open import FOTC.Data.List.Type

------------------------------------------------------------------------------

++-assoc : ∀ {xs ys zs} → List xs → List ys → List zs →
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc {xs} {ys} {zs} Lxs _ _ = indList P p[] is Lxs
  where
  P : D → Set
  P ds = (ds ++ ys) ++ zs ≡ ds ++ ys ++ zs
  {-# ATP definition P #-}

  postulate p[] : P []
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove p[] #-}

  postulate is : ∀ d {ds} → List ds → P ds → P (d ∷ ds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is #-}
