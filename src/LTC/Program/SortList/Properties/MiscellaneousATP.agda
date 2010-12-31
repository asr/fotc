------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.MiscellaneousATP where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Bool
  using ( _&&_
        ; Bool -- The LTC booleans type.
        )
open import LTC.Data.Bool.PropertiesATP
  using ( ≤-Bool
        ; &&-proj₁
        ; &&-proj₂
        )

open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.List.PropertiesATP using ( ++-ListN )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC list of natural numbers type.
        )
open import LTC.Data.List using ( _++_ ; ++-[] )

open import LTC.Program.SortList.Properties.Closures.BoolATP
  using ( ≤-ItemList-Bool
        ; ≤-Lists-Bool
        ; ordList-Bool
        )
open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
-- xs≤[] : {is : D} → ListN is → OrdList is → LE-Lists is []
-- xs≤[] nilLN                     _       = ≤-Lists-[] []
-- xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
--   prf $ xs≤[] LNis (subList-OrdList Ni LNis LOconsL)
--   where
--     postulate prf : LE-Lists is [] →  --IH.
--                     LE-Lists (i ∷ is) []
--     -- Metis 2.3 (release 20101019): No-success due to timeout (180 sec).
--     {-# ATP prove prf ≤-ItemList-Bool ordList-Bool x&&y≡true→x≡true #-}

x≤ys→x≤zs→x≤ys++zs : {i js ks : D} → N i → ListN js → ListN ks →
                     LE-ItemList i js →
                     LE-ItemList i ks →
                     LE-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni nilLN LNks _ i≤k =
  subst (λ t → LE-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  prf (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks (&&-proj₂ aux₁ aux₂ aux₃) i≤k)
  where
    aux₁ : Bool (i ≤ j)
    aux₁ = ≤-Bool Ni Nj

    aux₂ : Bool (≤-ItemList i js)
    aux₂ = ≤-ItemList-Bool Ni LNjs

    aux₃ : i ≤ j && (≤-ItemList i js) ≡ true
    aux₃ = trans (sym (≤-ItemList-∷ i j js)) i≤j∷js

    postulate prf : LE-ItemList i (js ++ ks) →  -- IH.
                    LE-ItemList i ((j ∷ js) ++ ks)
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf &&-proj₁ aux₁ aux₂ aux₃ #-}

xs≤ys→xs≤zs→xs≤ys++zs : {is js ks : D} → ListN is → ListN js → ListN ks →
                        LE-Lists is js →
                        LE-Lists is ks →
                        LE-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs nilLN LNjs LNks _ _ = ≤-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (consLN {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  prf ((xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                              (&&-proj₂ aux₁ aux₂ aux₃)
                              (&&-proj₂ aux₄ aux₅ aux₆)))
  where
    aux₁ = ≤-ItemList-Bool Ni LNjs
    aux₂ = ≤-Lists-Bool LNis LNjs
    aux₃ = trans (sym (≤-Lists-∷ i is js)) i∷is≤js

    aux₄ = ≤-ItemList-Bool Ni LNks
    aux₅ = ≤-Lists-Bool LNis LNks
    aux₆ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

    postulate prf : LE-Lists is (js ++ ks) →  -- IH.
                    LE-Lists (i ∷ is) (js ++ ks)
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf x≤ys→x≤zs→x≤ys++zs &&-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ #-}

xs≤zs→ys≤zs→xs++ys≤zs : {is js ks : D} → ListN is → ListN js → ListN ks →
                        LE-Lists is ks →
                        LE-Lists js ks →
                        LE-Lists (is ++ js) ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks} nilLN LNjs LNks is≤ks js≤ks =
  subst (λ t → LE-Lists t ks)
        (sym (++-[] js))
        js≤ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks}
                      (consLN {i} {is} Ni LNis) LNjs LNks i∷is≤ks js≤ks =
  prf (xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks (&&-proj₂ aux₁ aux₂ aux₃) js≤ks)
  where
    aux₁ = ≤-ItemList-Bool Ni LNks
    aux₂ = ≤-Lists-Bool LNis LNks
    aux₃ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

    postulate prf : LE-Lists (is ++ js) ks →  -- IH.
                    LE-Lists ((i ∷ is) ++ js) ks
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf &&-proj₁ aux₁ aux₂ aux₃ #-}
