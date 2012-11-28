------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdListATP where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesATP
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : ∀ {i is} → N i → ListN is → OrdList (i ∷ is) → OrdList is
subList-OrdList {i} Ni lnnil LOi∷is = ordList-[]

subList-OrdList {i} Ni (lncons {j} {js} Nj Ljs) LOi∷j∷js = prf
  where postulate prf : OrdList (j ∷ js)
        {-# ATP prove prf &&-list₂-t le-ItemList-Bool ordList-Bool #-}

++-OrdList-helper : ∀ {item is js} → N item → ListN is → ListN js →
                    ≤-ItemList item is →
                    ≤-ItemList item js →
                    ≤-Lists is js →
                    ≤-ItemList item (is ++ js)

++-OrdList-helper {item} {js = js} _ lnnil _ _ item≤js _ =
  subst (λ t → ≤-ItemList item t) (sym (++-leftIdentity js)) item≤js

++-OrdList-helper {item} {js = js} Nitem
                  (lncons {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  prf (++-OrdList-helper Nitem LNis LNjs lemma₁ item≤js lemma₂)
  where
  lemma₁ : le-ItemList item is ≡ true
  lemma₁ =  &&-list₂-t₂ (le-Bool Nitem Ni)
                        (le-ItemList-Bool Nitem LNis)
                        (trans (sym (le-ItemList-∷ item i is)) item≤i∷is)

  lemma₂ : le-Lists is js ≡ true
  lemma₂ = &&-list₂-t₂ (le-ItemList-Bool Ni LNjs)
                       (le-Lists-Bool LNis LNjs)
                       (trans (sym (le-Lists-∷ i is js)) i∷is≤js)

  postulate prf : ≤-ItemList item (is ++ js) →
                  ≤-ItemList item ((i ∷ is) ++ js)
  {-# ATP prove prf &&-list₂-t le-Bool le-ItemList-Bool #-}
