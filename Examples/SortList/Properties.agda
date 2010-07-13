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

open import LTC.Data.Nat.List
open import LTC.Data.Nat.Type

------------------------------------------------------------------------------

-- If (i ∷ is) is ordered then 'is' is ordered.
-- This function is defined in this module to avoid cyclical dependencies.
subList-ListOrd : {i : D} → N i → {is : D} → List is → ListOrd (i ∷ is) →
                  ListOrd is
subList-ListOrd {i} Ni nilL LOi∷is = isListOrd-[]

subList-ListOrd {i} Ni (consL {j} {js} Nj Ljs) LOi∷j∷js = prf
  where
    postulate prf : ListOrd (j ∷ js)
    {-# ATP prove prf x&&y≡true→y≡true ≤-ItemList-Bool isListOrd-Bool #-}

xs≤[] : {is : D} → List is → ListOrd is → LE-Lists is []
xs≤[] nilL _ = ≤-Lists-[] []
xs≤[] (consL {i} {is} Ni Lis) LOconsL =
  prf (xs≤[] Lis (subList-ListOrd Ni Lis LOconsL))
  where
    postulate prf : LE-Lists is []  → --IH.
                    LE-Lists (i ∷ is) []
    {-# ATP prove prf ≤-ItemList-Bool isListOrd-Bool x&&y≡true→x≡true #-}
