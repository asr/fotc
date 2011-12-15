------------------------------------------------------------------------------
-- Totality properties respect to OrdList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdListI where

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
open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : ∀ {i is} → N i → ListN is → OrdList (i ∷ is) → OrdList is
subList-OrdList {i} Ni nilLN LOi∷is = ordList-[]

subList-OrdList {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js =
  &&-proj₂ (≤-ItemList-Bool Ni (consLN Nj Ljs))
           (ordList-Bool (consLN Nj Ljs))
           (trans (sym $ ordList-∷ i (j ∷ js)) LOi∷j∷js)

++-OrdList-helper : ∀ {item is js} → N item → ListN is → ListN js →
                    LE-ItemList item is →
                    LE-ItemList item js →
                    LE-Lists is js →
                    LE-ItemList item (is ++ js)
++-OrdList-helper {item} {js = js} _ nilLN _ _ item≤js _ =
  subst (λ t → LE-ItemList item t) (sym (++-[] js)) item≤js

++-OrdList-helper {item} {js = js} Nitem
                  (consLN {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  begin
    ≤-ItemList item ((i ∷ is) ++ js)
      ≡⟨ subst (λ t → ≤-ItemList item ((i ∷ is) ++ js) ≡ ≤-ItemList item t)
               (++-∷ i is js)
               refl
      ⟩
    ≤-ItemList item (i ∷ (is ++ js))
      ≡⟨ ≤-ItemList-∷ item i (is ++ js) ⟩
    item ≤ i && ≤-ItemList item (is ++ js)
      ≡⟨ subst (λ t → item ≤ i && ≤-ItemList item (is ++ js) ≡
                      t && ≤-ItemList item (is ++ js))
               (&&-proj₁ (≤-Bool Nitem Ni)
                         (≤-ItemList-Bool Nitem LNis)
                         (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is))
               refl
      ⟩
    true && ≤-ItemList item (is ++ js)
      ≡⟨ subst (λ t → true && ≤-ItemList item (is ++ js) ≡ true && t)
               -- IH.
               (++-OrdList-helper Nitem LNis LNjs lemma₁ item≤js lemma₂)
               refl
      ⟩
    true && true ≡⟨ &&-tt ⟩
    true
  ∎
    where
    lemma₁ : ≤-ItemList item is ≡ true
    lemma₁ =  &&-proj₂ (≤-Bool Nitem Ni)
                       (≤-ItemList-Bool Nitem LNis)
                       (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)

    lemma₂ : ≤-Lists is js ≡ true
    lemma₂ = &&-proj₂ (≤-ItemList-Bool Ni LNjs)
                      (≤-Lists-Bool LNis LNjs)
                      (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)
