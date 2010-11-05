------------------------------------------------------------------------------
--  Properties related with lists (using induction on the LTC list type)
------------------------------------------------------------------------------

module LTC.Data.List.PropertiesByInduction where

open import LTC.Base

open import LTC.Data.List
  using ( _++_
        ; indList
        ; List  -- The LTC list type.
        )
-- TODO: There is a bug with the importation in agda2atp.
open import LTC.Data.List.Type using ()

------------------------------------------------------------------------------
++-assoc : {xs ys zs : D} → List xs → List ys → List zs →
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc {xs} {ys} {zs} Lxs _ _ = indList P p[] iStep Lxs
  where
    P : D → Set
    P ds = (ds ++ ys) ++ zs ≡ ds ++ ys ++ zs
    {-# ATP definition P #-}

    postulate
      p[] : P []
    {-# ATP prove p[] #-}

    postulate
      iStep : (d : D){ds : D} → List ds → P ds → P (d ∷ ds)
    {-# ATP prove iStep #-}
