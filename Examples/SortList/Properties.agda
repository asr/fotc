------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

module Examples.SortList.Properties where

open import LTC.Minimal

open import Examples.SortList.Closures.Bool using
  ( ≤-ItemList-Bool
  ; isListOrd-Bool
  )
open import Examples.SortList.SortList using
  ( ≤-Lists-[]
  ; isListOrd ; isListOrd-[] ; isListOrd-∷
  ; LE-Lists
  ; ListOrd
  )

open import LTC.Data.Bool.Properties using
  ( x&&y≡true→x≡true
  ; x&&y≡true→y≡true
  )

open import LTC.Data.Nat.List.Properties using ( ++-ListN )
open import LTC.Data.Nat.List.Type using
  ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
  )
open import LTC.Data.Nat.Type using ( N )
open import LTC.Data.List using ( _++_ )

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
-- This function is defined in this module to avoid cyclical dependencies.
subList-ListOrd : {i : D} → N i → {is : D} → ListN is → ListOrd (i ∷ is) →
                  ListOrd is
subList-ListOrd {i} Ni nilLN LOi∷is = isListOrd-[]

subList-ListOrd {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js = prf
  where
    postulate prf : ListOrd (j ∷ js)
    -- E 1.2 no-success due to timeout (300).
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

listOrd-xs++ys→ys≤zs→xs++ys≤zs :
  {is js ks : D} → ListN is → ListN js → ListN ks → ListOrd (is ++ js) →
  LE-Lists js ks → LE-Lists (is ++ js) ks

listOrd-xs++ys→ys≤zs→xs++ys≤zs
  {js = js} {ks = ks} nilLN LNjs LNks LOis++js js≤ks = prf
  where
    postulate prf : LE-Lists ([] ++ js) ks
    {-# ATP prove prf #-}

listOrd-xs++ys→ys≤zs→xs++ys≤zs
  {js = js} {ks = ks} (consLN {i} {is} Ni LNis) LNjs LNks LOi∷is++js js≤ks =
  prf (listOrd-xs++ys→ys≤zs→xs++ys≤zs LNis LNjs LNks
         (x&&y≡true→y≡true (≤-ItemList-Bool Ni (++-ListN LNis LNjs))
                           (isListOrd-Bool (++-ListN LNis LNjs))
                           (trans (sym (isListOrd-∷ i (is ++ js)))
                                  (trans aux LOi∷is++js)))
                           js≤ks)
  where
    postulate prf :  LE-Lists (is ++ js) ks → -- IH
                     LE-Lists ((i ∷ is) ++ js) ks
    -- E 1.2 no-success due to timeout (300).
    {-# ATP prove prf ≤-ItemList-Bool isListOrd-Bool x&&y≡true→x≡true
                      ++-ListN
    #-}

    postulate aux : isListOrd (i ∷ is ++ js) ≡ isListOrd ((i ∷ is) ++ js)
    {-# ATP prove aux #-}
