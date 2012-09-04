------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdListI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : ∀ {i is} → N i → ListN is → OrdList (i ∷ is) → OrdList is
subList-OrdList {i} Ni lnnil LOi∷is = ordList-[]

subList-OrdList {i} Ni (lncons {j} {js} Nj Ljs) LOi∷j∷js =
  &&-list₂-t₂ (≤-ItemList-Bool Ni (lncons Nj Ljs))
              (ordList-Bool (lncons Nj Ljs))
              (trans (sym $ ordList-∷ i (j ∷ js)) LOi∷j∷js)

++-OrdList-helper : ∀ {item is js} → N item → ListN is → ListN js →
                    LE-ItemList item is →
                    LE-ItemList item js →
                    LE-Lists is js →
                    LE-ItemList item (is ++ js)
++-OrdList-helper {item} {js = js} _ lnnil _ _ item≤js _ =
  subst (λ t → LE-ItemList item t) (sym (++-[] js)) item≤js

++-OrdList-helper {item} {js = js} Nitem
                  (lncons {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  ≤-ItemList item ((i ∷ is) ++ js)
    ≡⟨ subst (λ t → ≤-ItemList item ((i ∷ is) ++ js) ≡ ≤-ItemList item t)
             (++-∷ i is js)
             refl
    ⟩
  ≤-ItemList item (i ∷ (is ++ js))
    ≡⟨ ≤-ItemList-∷ item i (is ++ js) ⟩
  (item ≤ i) && ≤-ItemList item (is ++ js)
    ≡⟨ subst (λ t → (item ≤ i) && ≤-ItemList item (is ++ js) ≡
                    t && ≤-ItemList item (is ++ js))
             (&&-list₂-t₁ (≤-Bool Nitem Ni)
                          (≤-ItemList-Bool Nitem LNis)
                          (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is))
             refl
    ⟩
  true && ≤-ItemList item (is ++ js)
    ≡⟨ subst (λ t → true && ≤-ItemList item (is ++ js) ≡ true && t)
             (++-OrdList-helper Nitem LNis LNjs lemma₁ item≤js lemma₂)
             refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
    where
    lemma₁ : ≤-ItemList item is ≡ true
    lemma₁ =  &&-list₂-t₂ (≤-Bool Nitem Ni)
                          (≤-ItemList-Bool Nitem LNis)
                          (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)

    lemma₂ : ≤-Lists is js ≡ true
    lemma₂ = &&-list₂-t₂ (≤-ItemList-Bool Ni LNjs)
                         (≤-Lists-Bool LNis LNjs)
                         (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)
