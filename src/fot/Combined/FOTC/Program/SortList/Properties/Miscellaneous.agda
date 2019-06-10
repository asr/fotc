------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.SortList.Properties.Miscellaneous where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.Bool.Properties
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.List.Properties
open import Combined.FOTC.Data.Nat.List.Type
open import Combined.FOTC.Data.Nat.Type
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.List.Properties
open import Combined.FOTC.Program.SortList.Properties.Totality.Bool
open import Combined.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall 1969,
-- p. 46).
-- xs≤[] : ∀ {is} → ListN is → OrdList is → ≤-Lists is []
-- xs≤[] nilLN                     _       = ≤-Lists-[] []
-- xs≤[] (lncons {i} {is} Ni LNis) LOconsL =
--   prf $ xs≤[] LNis (subList-OrdList Ni LNis LOconsL)
--   where
--     postulate prf : ≤-Lists is [] →  --IH.
--                     ≤-Lists (i ∷ is) []
--     {-# ATP prove prf ≤-ItemList-Bool ordList-Bool x&&y≡true→x≡true #-}

x≤ys→x≤zs→x≤ys++zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                     ≤-ItemList i js →
                     ≤-ItemList i ks →
                     ≤-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni lnnil LNks _ i≤k =
  subst (≤-ItemList i) (sym (++-leftIdentity ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (lncons {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  prf (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks (&&-list₂-t₂ helper₁ helper₂ helper₃) i≤k)
  where
  helper₁ : Bool (le i j)
  helper₁ = le-Bool Ni Nj

  helper₂ : Bool (le-ItemList i js)
  helper₂ = le-ItemList-Bool Ni LNjs

  helper₃ : le i j && le-ItemList i js ≡ true
  helper₃ = trans (sym (le-ItemList-∷ i j js)) i≤j∷js

  postulate prf : ≤-ItemList i (js ++ ks) → ≤-ItemList i ((j ∷ js) ++ ks)
  {-# ATP prove prf &&-list₂-t helper₁ helper₂ helper₃ #-}

xs≤ys→xs≤zs→xs≤ys++zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        ≤-Lists is js →
                        ≤-Lists is ks →
                        ≤-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs lnnil LNjs LNks _ _ = le-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (lncons {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  prf ((xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                              (&&-list₂-t₂ helper₁ helper₂ helper₃)
                              (&&-list₂-t₂ helper₄ helper₅ helper₆)))
  where
  helper₁ = le-ItemList-Bool Ni LNjs
  helper₂ = le-Lists-Bool LNis LNjs
  helper₃ = trans (sym (le-Lists-∷ i is js)) i∷is≤js

  helper₄ = le-ItemList-Bool Ni LNks
  helper₅ = le-Lists-Bool LNis LNks
  helper₆ = trans (sym (le-Lists-∷ i is ks)) i∷is≤ks

  postulate prf : ≤-Lists is (js ++ ks) → ≤-Lists (i ∷ is) (js ++ ks)
  {-# ATP prove prf x≤ys→x≤zs→x≤ys++zs &&-list₂-t helper₁ helper₂ helper₃ helper₄ helper₅ helper₆ #-}

xs≤zs→ys≤zs→xs++ys≤zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        ≤-Lists is ks →
                        ≤-Lists js ks →
                        ≤-Lists (is ++ js) ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks} lnnil LNjs LNks is≤ks js≤ks =
  subst (λ t → ≤-Lists t ks)
        (sym (++-leftIdentity js))
        js≤ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks}
                      (lncons {i} {is} Ni LNis) LNjs LNks i∷is≤ks js≤ks =
  prf (xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks
                             (&&-list₂-t₂ helper₁ helper₂ helper₃)
                             js≤ks)
  where
  helper₁ = le-ItemList-Bool Ni LNks
  helper₂ = le-Lists-Bool LNis LNks
  helper₃ = trans (sym (le-Lists-∷ i is ks)) i∷is≤ks

  postulate prf : ≤-Lists (is ++ js) ks → ≤-Lists ((i ∷ is) ++ js) ks
  {-# ATP prove prf &&-list₂-t helper₁ helper₂ helper₃ #-}

------------------------------------------------------------------------------
-- References
--
-- Burstall, R. M. (1969). Proving properties of programs by
-- structural induction. The Computer Journal 12.1, pp. 41–48.
