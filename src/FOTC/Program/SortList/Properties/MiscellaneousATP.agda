------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • R. M. Burstall. Proving properties of programs by structural
--   induction. The Computer Journal, 12(1):41–48, 1969.

module FOTC.Program.SortList.Properties.MiscellaneousATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall 1969,
-- p. 46).
-- xs≤[] : ∀ {is} → ListN is → OrdList is → LE-Lists is []
-- xs≤[] nilLN                     _       = ≤-Lists-[] []
-- xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
--   prf $ xs≤[] LNis (subList-OrdList Ni LNis LOconsL)
--   where
--     postulate prf : LE-Lists is [] →  --IH.
--                     LE-Lists (i ∷ is) []
--     {-# ATP prove prf ≤-ItemList-Bool ordList-Bool x&&y≡true→x≡true #-}

x≤ys→x≤zs→x≤ys++zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                     LE-ItemList i js →
                     LE-ItemList i ks →
                     LE-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni nilLN LNks _ i≤k =
  subst (λ t → LE-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  prf (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks (&&-list₂-t₂ helper₁ helper₂ helper₃) i≤k)
  where
  helper₁ : Bool (i ≤ j)
  helper₁ = ≤-Bool Ni Nj

  helper₂ : Bool (≤-ItemList i js)
  helper₂ = ≤-ItemList-Bool Ni LNjs

  helper₃ : (i ≤ j) && ≤-ItemList i js ≡ true
  helper₃ = trans (sym (≤-ItemList-∷ i j js)) i≤j∷js

  postulate prf : LE-ItemList i (js ++ ks) →  -- IH.
                  LE-ItemList i ((j ∷ js) ++ ks)
  {-# ATP prove prf &&-list₂-t helper₁ helper₂ helper₃ #-}

xs≤ys→xs≤zs→xs≤ys++zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        LE-Lists is js →
                        LE-Lists is ks →
                        LE-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs nilLN LNjs LNks _ _ = ≤-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (consLN {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  prf ((xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                              (&&-list₂-t₂ helper₁ helper₂ helper₃)
                              (&&-list₂-t₂ helper₄ helper₅ helper₆)))
  where
  helper₁ = ≤-ItemList-Bool Ni LNjs
  helper₂ = ≤-Lists-Bool LNis LNjs
  helper₃ = trans (sym (≤-Lists-∷ i is js)) i∷is≤js

  helper₄ = ≤-ItemList-Bool Ni LNks
  helper₅ = ≤-Lists-Bool LNis LNks
  helper₆ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

  postulate prf : LE-Lists is (js ++ ks) →  -- IH.
                  LE-Lists (i ∷ is) (js ++ ks)
  {-# ATP prove prf x≤ys→x≤zs→x≤ys++zs &&-list₂-t
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
                             (&&-list₂-t₂ helper₁ helper₂ helper₃)
                             js≤ks)
  where
  helper₁ = ≤-ItemList-Bool Ni LNks
  helper₂ = ≤-Lists-Bool LNis LNks
  helper₃ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

  postulate prf : LE-Lists (is ++ js) ks →  -- IH.
                  LE-Lists ((i ∷ is) ++ js) ks
  {-# ATP prove prf &&-list₂-t helper₁ helper₂ helper₃ #-}
