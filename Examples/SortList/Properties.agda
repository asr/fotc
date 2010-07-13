------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

module Examples.SortList.Properties where

open import LTC.Minimal

open import Examples.SortList.Closures.Bool using
  ( ≤-ItemList-Bool ; isListOrd-Bool )
open import Examples.SortList.SortList

open import LTC.Data.Bool.PropertiesER using
  ( x&&y≡true→x≡true ; x&&y≡true→y≡true )

open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.Type
open import LTC.Data.List

------------------------------------------------------------------------------

-- If (i ∷ is) is ordered then 'is' is ordered.
-- This function is defined in this module to avoid cyclical dependencies.
subList-ListOrd : {i : D} → N i → {is : D} → ListN is → ListOrd (i ∷ is) →
                  ListOrd is
subList-ListOrd {i} Ni nilLN LOi∷is = isListOrd-[]

subList-ListOrd {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js = prf
  where
    postulate prf : ListOrd (j ∷ js)
    {-# ATP prove prf x&&y≡true→y≡true ≤-ItemList-Bool isListOrd-Bool #-}

-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
xs≤[] : {is : D} → ListN is → ListOrd is → LE-Lists is []
xs≤[] nilLN                     _       = ≤-Lists-[] []
xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
  prf (xs≤[] LNis (subList-ListOrd Ni LNis LOconsL))
  where
    postulate prf : LE-Lists is []  → --IH.
                    LE-Lists (i ∷ is) []
    {-# ATP prove prf ≤-ItemList-Bool isListOrd-Bool x&&y≡true→x≡true #-}
