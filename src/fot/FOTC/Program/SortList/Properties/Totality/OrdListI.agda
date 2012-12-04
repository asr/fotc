------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdListI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : ∀ {i is} → N i → ListN is → OrdList (i ∷ is) → OrdList is
subList-OrdList {i} Ni lnnil LOi∷is = ordList-[]

subList-OrdList {i} Ni (lncons {j} {js} Nj Ljs) LOi∷j∷js =
  &&-list₂-t₂ (le-ItemList-Bool Ni (lncons Nj Ljs))
              (ordList-Bool (lncons Nj Ljs))
              (trans (sym (ordList-∷ i (j ∷ js))) LOi∷j∷js)

++-OrdList-helper : ∀ {item is js} → N item → ListN is → ListN js →
                    ≤-ItemList item is →
                    ≤-ItemList item js →
                    ≤-Lists is js →
                    ≤-ItemList item (is ++ js)
++-OrdList-helper {item} {js = js} _ lnnil _ _ item≤js _ =
  subst (λ t → ≤-ItemList item t) (sym (++-leftIdentity js)) item≤js

++-OrdList-helper {item} {js = js} Nitem
                  (lncons {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  le-ItemList item ((i ∷ is) ++ js)
    ≡⟨ subst (λ t → le-ItemList item ((i ∷ is) ++ js) ≡ le-ItemList item t)
             (++-∷ i is js)
             refl
    ⟩
  le-ItemList item (i ∷ (is ++ js))
    ≡⟨ le-ItemList-∷ item i (is ++ js) ⟩
  le item i && le-ItemList item (is ++ js)
    ≡⟨ subst (λ t → le item i && le-ItemList item (is ++ js) ≡
                    t && le-ItemList item (is ++ js))
             (&&-list₂-t₁ (le-Bool Nitem Ni)
                          (le-ItemList-Bool Nitem LNis)
                          (trans (sym (le-ItemList-∷ item i is)) item≤i∷is))
             refl
    ⟩
  true && le-ItemList item (is ++ js)
    ≡⟨ subst (λ t → true && le-ItemList item (is ++ js) ≡ true && t)
             (++-OrdList-helper Nitem LNis LNjs lemma₁ item≤js lemma₂)
             refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
    where
    lemma₁ : le-ItemList item is ≡ true
    lemma₁ =  &&-list₂-t₂ (le-Bool Nitem Ni)
                          (le-ItemList-Bool Nitem LNis)
                          (trans (sym (le-ItemList-∷ item i is)) item≤i∷is)

    lemma₂ : le-Lists is js ≡ true
    lemma₂ = &&-list₂-t₂ (le-ItemList-Bool Ni LNjs)
                         (le-Lists-Bool LNis LNjs)
                         (trans (sym (le-Lists-∷ i is js)) i∷is≤js)
