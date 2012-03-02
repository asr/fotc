------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- TODO: It seems this module is not used.
module FOTC.Program.SortList.Properties.MiscellaneousI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.List.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
-- xs≤[] : ∀ {is} → ListN is → OrdList is → LE-Lists is []
-- xs≤[] nilLN                     _       = ≤-Lists-[] []
-- xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
--   begin
--     ≤-Lists (i ∷ is) []
--       ≡⟨ ≤-Lists-∷ i is [] ⟩
--     ≤-ItemList i [] && ≤-Lists is []
--       ≡⟨ subst (λ t → ≤-ItemList i [] && ≤-Lists is [] ≡ t && ≤-Lists is [])
--                (≤-ItemList-[] i)
--                refl
--       ⟩
--     true && ≤-Lists is []
--       ≡⟨ subst (λ t → true && ≤-Lists is [] ≡ true && t)
--                (xs≤[] LNis (subList-OrdList Ni LNis LOconsL))  -- IH.
--                refl
--       ⟩
--     true && true
--       ≡⟨ &&-tt ⟩
--     true
--   ∎

x≤ys++zs→x≤zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                LE-ItemList i (js ++ ks) → LE-ItemList i ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni nilLN LNks  i≤[]++ks =
  subst (λ t → LE-ItemList i t) (++-[] ks) i≤[]++ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js++ks =
  x≤ys++zs→x≤zs Ni LNjs LNks lemma₂
  where
  lemma₁ : i ≤ j && ≤-ItemList i (js ++ ks) ≡ true
  lemma₁ =
    i ≤ j && ≤-ItemList i (js ++ ks)
      ≡⟨ sym (≤-ItemList-∷ i j (js ++ ks)) ⟩
    ≤-ItemList i (j ∷ (js ++ ks))
      ≡⟨ subst (λ t → ≤-ItemList i (j ∷ (js ++ ks)) ≡ ≤-ItemList i t )
               (sym (++-∷ j js ks))
               refl
      ⟩
    ≤-ItemList i ((j ∷ js) ++ ks) ≡⟨ i≤j∷js++ks ⟩
    true ∎

  lemma₂ : LE-ItemList i (js ++ ks)
  lemma₂ = &&-proj₂ (≤-Bool Ni Nj)
                    (≤-ItemList-Bool Ni (++-ListN LNjs LNks))
                    lemma₁

xs++ys-OrdList→xs≤ys : ∀ {is js} → ListN is → ListN js →
                       OrdList (is ++ js) → LE-Lists is js
xs++ys-OrdList→xs≤ys {js = js} nilLN LNjs OLis++js =  ≤-Lists-[] js
xs++ys-OrdList→xs≤ys {js = js} (consLN {i} {is} Ni LNis) LNjs OLis++js =
  ≤-Lists (i ∷ is) js
    ≡⟨ ≤-Lists-∷ i is js ⟩
  ≤-ItemList i js && ≤-Lists is js
    ≡⟨ subst (λ t → ≤-ItemList i js && ≤-Lists is js ≡
                    t && ≤-Lists is js)
             (x≤ys++zs→x≤zs Ni LNis LNjs lemma₁)
             refl
    ⟩
  true && ≤-Lists is js
    ≡⟨ subst (λ t → true && ≤-Lists is js ≡ true && t)
             (xs++ys-OrdList→xs≤ys LNis LNjs lemma₂)  --IH.
             refl
    ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎
  where
  lemma₀ : ≤-ItemList i (is ++ js) && ordList (is ++ js) ≡ true
  lemma₀ = trans (sym (ordList-∷ i (is ++ js)))
                 (trans (subst (λ t → ordList (i ∷ is ++ js) ≡ ordList t)
                               (sym (++-∷ i is js))
                               refl)
                 OLis++js)

  helper₁ : Bool (≤-ItemList i (is ++ js))
  helper₁ = ≤-ItemList-Bool Ni (++-ListN LNis LNjs)

  helper₂ : Bool (ordList (is ++ js))
  helper₂ = ordList-Bool (++-ListN LNis LNjs)

  lemma₁ : ≤-ItemList i (is ++ js) ≡ true
  lemma₁ = &&-proj₁ helper₁ helper₂ lemma₀

  lemma₂ : ordList (is ++ js) ≡ true
  lemma₂ = &&-proj₂ helper₁ helper₂ lemma₀

x≤ys→x≤zs→x≤ys++zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                     LE-ItemList i js →
                     LE-ItemList i ks →
                     LE-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni nilLN LNks _ i≤k =
  subst (λ t → LE-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  ≤-ItemList i ((j ∷ js) ++ ks)
    ≡⟨ subst (λ t → ≤-ItemList i ((j ∷ js) ++ ks) ≡
                    ≤-ItemList i t)
             (++-∷ j js ks)
             refl
    ⟩
  ≤-ItemList i (j ∷ (js ++ ks))
    ≡⟨ ≤-ItemList-∷ i j (js ++ ks) ⟩
  i ≤ j && ≤-ItemList i (js ++ ks)
    ≡⟨ subst₂ (λ t₁ t₂ → i ≤ j && ≤-ItemList i (js ++ ks) ≡ t₁ && t₂)
              (&&-proj₁ helper₁ helper₂ helper₃)
              -- IH.
              (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks
                                  (&&-proj₂ helper₁ helper₂ helper₃)
                                  i≤k)
              refl
    ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎
  where
  helper₁ : Bool (i ≤ j)
  helper₁ = ≤-Bool Ni Nj

  helper₂ : Bool (≤-ItemList i js)
  helper₂ = ≤-ItemList-Bool Ni LNjs

  helper₃ : i ≤ j && (≤-ItemList i js) ≡ true
  helper₃ = trans (sym (≤-ItemList-∷ i j js)) i≤j∷js

xs≤ys→xs≤zs→xs≤ys++zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        LE-Lists is js →
                        LE-Lists is ks →
                        LE-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs nilLN LNjs LNks _ _ = ≤-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (consLN {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  ≤-Lists (i ∷ is) (js ++ ks)
    ≡⟨ ≤-Lists-∷ i is (js ++ ks)  ⟩
  ≤-ItemList i (js ++ ks) && ≤-Lists is (js ++ ks)
    ≡⟨ subst (λ t → ≤-ItemList i (js ++ ks) && ≤-Lists is (js ++ ks) ≡
                    t                       && ≤-Lists is (js ++ ks))
             (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks
                                 (&&-proj₁ helper₁ helper₂ helper₃)
                                 (&&-proj₁ helper₄ helper₅ helper₆))
             refl
    ⟩
  true && ≤-Lists is (js ++ ks)
    ≡⟨ subst (λ t → true && ≤-Lists is (js ++ ks) ≡ true && t)
             -- IH.
             (xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                                    (&&-proj₂ helper₁ helper₂ helper₃)
                                    (&&-proj₂ helper₄ helper₅ helper₆))
             refl
    ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎
  where
  helper₁ = ≤-ItemList-Bool Ni LNjs
  helper₂ = ≤-Lists-Bool LNis LNjs
  helper₃ = trans (sym (≤-Lists-∷ i is js)) i∷is≤js

  helper₄ = ≤-ItemList-Bool Ni LNks
  helper₅ = ≤-Lists-Bool LNis LNks
  helper₆ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

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
  ≤-Lists ((i ∷ is) ++ js) ks
    ≡⟨ subst (λ t → ≤-Lists ((i ∷ is) ++ js) ks ≡ ≤-Lists t ks)
             (++-∷ i is js)
             refl
    ⟩
    ≤-Lists (i ∷ (is ++ js)) ks
    ≡⟨ ≤-Lists-∷ i (is ++ js) ks ⟩
  ≤-ItemList i ks && ≤-Lists (is ++ js) ks
    ≡⟨ subst₂ (λ x y → ≤-ItemList i ks && ≤-Lists (is ++ js) ks ≡ x && y)
              LE-ItemList-i-ks
              LE-Lists-is++js-ks
              refl
    ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎
  where
  helper₁ = ≤-ItemList-Bool Ni LNks
  helper₂ = ≤-Lists-Bool LNis LNks
  helper₃ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

  LE-ItemList-i-ks : LE-ItemList i ks
  LE-ItemList-i-ks = &&-proj₁ helper₁ helper₂ helper₃

  -- IH.
  LE-Lists-is++js-ks : LE-Lists (is ++ js) ks
  LE-Lists-is++js-ks =
    xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks
                          (&&-proj₂ helper₁ helper₂ helper₃)
                          js≤ks
