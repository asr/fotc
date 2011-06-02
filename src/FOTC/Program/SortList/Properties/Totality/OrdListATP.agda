------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.OrdListATP where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Bool.PropertiesATP

open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List

open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : ∀ {i is} → N i → ListN is → OrdList (i ∷ is) → OrdList is
subList-OrdList {i} Ni nilLN LOi∷is = ordList-[]

subList-OrdList {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js = prf
  where
  postulate prf : OrdList (j ∷ js)
  -- E 1.2: Non-tested.
  -- Equinox 5.0alpha (2010-06-29): Non-tested.
  -- Metis 2.3 : Non-tested.
  {-# ATP prove prf &&-proj₂ ≤-ItemList-Bool ordList-Bool #-}

++-OrdList-helper : ∀ {item is js} → N item → ListN is → ListN js →
                    LE-ItemList item is →
                    LE-ItemList item js →
                    LE-Lists is js →
                    LE-ItemList item (is ++ js)

++-OrdList-helper {item} {js = js} _ nilLN _ _ item≤js _ =
  subst (λ t → LE-ItemList item t) (sym (++-[] js)) item≤js

++-OrdList-helper {item} {js = js} Nitem
                  (consLN {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  prf (++-OrdList-helper Nitem LNis LNjs lemma₁ item≤js lemma₂)
  where
  lemma₁ : ≤-ItemList item is ≡ true
  lemma₁ =  &&-proj₂ (≤-Bool Nitem Ni)
                     (≤-ItemList-Bool Nitem LNis)
                     (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)

  lemma₂ : ≤-Lists is js ≡ true
  lemma₂ = &&-proj₂ (≤-ItemList-Bool Ni LNjs)
                    (≤-Lists-Bool LNis LNjs)
                    (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)

  postulate prf : LE-ItemList item (is ++ js) →  -- IH.
                  LE-ItemList item ((i ∷ is) ++ js)
  -- E 1.2: Non-tested.
  -- Metis 2.3 : Non-tested.
  -- Vampire 0.6 (revision 903): Non-tested.
  {-# ATP prove prf ≤-Bool ≤-ItemList-Bool &&-proj₁ #-}
