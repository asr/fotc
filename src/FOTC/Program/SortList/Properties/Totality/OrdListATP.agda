------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdListATP where

open import Common.Function

open import FOTC.Base
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
  {-# ATP prove prf &&-list₂-true ≤-ItemList-Bool ordList-Bool #-}

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
  lemma₁ =  &&-list₂-true₂ (≤-Bool Nitem Ni)
                           (≤-ItemList-Bool Nitem LNis)
                           (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)

  lemma₂ : ≤-Lists is js ≡ true
  lemma₂ = &&-list₂-true₂ (≤-ItemList-Bool Ni LNjs)
                          (≤-Lists-Bool LNis LNjs)
                          (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)

  postulate prf : LE-ItemList item (is ++ js) →  -- IH.
                  LE-ItemList item ((i ∷ is) ++ js)
  {-# ATP prove prf ≤-Bool ≤-ItemList-Bool &&-list₂-true #-}
