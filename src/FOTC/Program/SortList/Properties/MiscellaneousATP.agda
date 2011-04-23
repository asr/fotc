------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.MiscellaneousATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Bool
  using ( _&&_
        ; Bool -- The FOTC booleans type.
        )
open import FOTC.Data.Bool.PropertiesATP
  using ( ≤-Bool
        ; &&-proj₁
        ; &&-proj₂
        )

open import FOTC.Data.Nat.Inequalities using ( _≤_ )
open import FOTC.Data.Nat.List.PropertiesATP using ( ++-ListN )
open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.List using ( _++_ ; ++-[] )

open import FOTC.Program.SortList.Properties.Totality.BoolATP
  using ( ≤-ItemList-Bool
        ; ≤-Lists-Bool
        ; ordList-Bool
        )
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
-- xs≤[] : ∀ {is} → ListN is → OrdList is → LE-Lists is []
-- xs≤[] nilLN                     _       = ≤-Lists-[] []
-- xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
--   prf $ xs≤[] LNis (subList-OrdList Ni LNis LOconsL)
--   where
--     postulate prf : LE-Lists is [] →  --IH.
--                     LE-Lists (i ∷ is) []
--     -- Metis 2.3 (release 20101019): No-success due to timeout (180 sec).
--     {-# ATP prove prf ≤-ItemList-Bool ordList-Bool x&&y≡true→x≡true #-}

x≤ys→x≤zs→x≤ys++zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                     LE-ItemList i js →
                     LE-ItemList i ks →
                     LE-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni nilLN LNks _ i≤k =
  subst (λ t → LE-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  prf (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks (&&-proj₂ helper₁ helper₂ helper₃) i≤k)
  where
    helper₁ : Bool (i ≤ j)
    helper₁ = ≤-Bool Ni Nj

    helper₂ : Bool (≤-ItemList i js)
    helper₂ = ≤-ItemList-Bool Ni LNjs

    helper₃ : i ≤ j && (≤-ItemList i js) ≡ true
    helper₃ = trans (sym (≤-ItemList-∷ i j js)) i≤j∷js

    postulate prf : LE-ItemList i (js ++ ks) →  -- IH.
                    LE-ItemList i ((j ∷ js) ++ ks)
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf &&-proj₁ helper₁ helper₂ helper₃ #-}

xs≤ys→xs≤zs→xs≤ys++zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        LE-Lists is js →
                        LE-Lists is ks →
                        LE-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs nilLN LNjs LNks _ _ = ≤-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (consLN {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  prf ((xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                              (&&-proj₂ helper₁ helper₂ helper₃)
                              (&&-proj₂ helper₄ helper₅ helper₆)))
  where
    helper₁ = ≤-ItemList-Bool Ni LNjs
    helper₂ = ≤-Lists-Bool LNis LNjs
    helper₃ = trans (sym (≤-Lists-∷ i is js)) i∷is≤js

    helper₄ = ≤-ItemList-Bool Ni LNks
    helper₅ = ≤-Lists-Bool LNis LNks
    helper₆ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

    postulate prf : LE-Lists is (js ++ ks) →  -- IH.
                    LE-Lists (i ∷ is) (js ++ ks)
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf x≤ys→x≤zs→x≤ys++zs &&-proj₁
                      helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
    #-}

xs≤zs→ys≤zs→xs++ys≤zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        LE-Lists is ks →
                        LE-Lists js ks →
                        LE-Lists (is ++ js) ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks} nilLN LNjs LNks is≤ks js≤ks =
  subst (λ t → LE-Lists t ks)
        (sym (++-[] js))
        js≤ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks}
                      (consLN {i} {is} Ni LNis) LNjs LNks i∷is≤ks js≤ks =
  prf (xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks
                             (&&-proj₂ helper₁ helper₂ helper₃)
                             js≤ks)
  where
    helper₁ = ≤-ItemList-Bool Ni LNks
    helper₂ = ≤-Lists-Bool LNis LNks
    helper₃ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

    postulate prf : LE-Lists (is ++ js) ks →  -- IH.
                    LE-Lists ((i ∷ is) ++ js) ks
    -- E 1.2: Non-tested.
    -- Metis 2.3 (release 20101019): Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf &&-proj₁ helper₁ helper₂ helper₃ #-}
