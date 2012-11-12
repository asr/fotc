------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • R. M. Burstall. Proving properties of programs by structural
--   induction. The Computer Journal, 12(1):41–48, 1969.

module FOTC.Program.SortList.Properties.MiscellaneousI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open FOTC.Base.BList
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
-- lists is only an ordering if nil is excluded" (Burstall 1969,
-- p. 46).
-- xs≤[] : ∀ {is} → ListN is → OrdList is → LE-Lists is []
-- xs≤[] lnnil                     _       = ≤-Lists-[] []
-- xs≤[] (lncons {i} {is} Ni LNis) LOconsL =
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
--                (xs≤[] LNis (subList-OrdList Ni LNis LOconsL))
--                refl
--       ⟩
--     true && true
--       ≡⟨ &&-tt ⟩
--     true
--   ∎

x≤ys++zs→x≤zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                ≤-ItemList i (js ++ ks) → ≤-ItemList i ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni lnnil LNks  i≤[]++ks =
  subst (λ t → ≤-ItemList i t) (++-[] ks) i≤[]++ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni (lncons {j} {js} Nj LNjs) LNks i≤j∷js++ks =
  x≤ys++zs→x≤zs Ni LNjs LNks lemma₂
  where
  lemma₁ : le i j && le-ItemList i (js ++ ks) ≡ true
  lemma₁ =
    le i j && le-ItemList i (js ++ ks)
      ≡⟨ sym (le-ItemList-∷ i j (js ++ ks)) ⟩
    le-ItemList i (j ∷ (js ++ ks))
      ≡⟨ subst (λ t → le-ItemList i (j ∷ (js ++ ks)) ≡ le-ItemList i t )
               (sym (++-∷ j js ks))
               refl
      ⟩
    le-ItemList i ((j ∷ js) ++ ks) ≡⟨ i≤j∷js++ks ⟩
    true ∎

  lemma₂ : ≤-ItemList i (js ++ ks)
  lemma₂ = &&-list₂-t₂ (le-Bool Ni Nj)
                       (le-ItemList-Bool Ni (++-ListN LNjs LNks))
                       lemma₁

xs++ys-OrdList→xs≤ys : ∀ {is js} → ListN is → ListN js →
                       OrdList (is ++ js) → ≤-Lists is js
xs++ys-OrdList→xs≤ys {js = js} lnnil LNjs OLis++js = le-Lists-[] js
xs++ys-OrdList→xs≤ys {js = js} (lncons {i} {is} Ni LNis) LNjs OLis++js =
  le-Lists (i ∷ is) js
    ≡⟨ le-Lists-∷ i is js ⟩
  le-ItemList i js && le-Lists is js
    ≡⟨ subst (λ t → le-ItemList i js && le-Lists is js ≡
                    t && le-Lists is js)
             (x≤ys++zs→x≤zs Ni LNis LNjs lemma₁)
             refl
    ⟩
  true && le-Lists is js
    ≡⟨ subst (λ t → true && le-Lists is js ≡ true && t)
             (xs++ys-OrdList→xs≤ys LNis LNjs lemma₂)  --IH.
             refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
  where
  lemma₀ : le-ItemList i (is ++ js) && ordList (is ++ js) ≡ true
  lemma₀ = trans (sym (ordList-∷ i (is ++ js)))
                 (trans (subst (λ t → ordList (i ∷ is ++ js) ≡ ordList t)
                               (sym (++-∷ i is js))
                               refl)
                 OLis++js)

  helper₁ : Bool (le-ItemList i (is ++ js))
  helper₁ = le-ItemList-Bool Ni (++-ListN LNis LNjs)

  helper₂ : Bool (ordList (is ++ js))
  helper₂ = ordList-Bool (++-ListN LNis LNjs)

  lemma₁ : le-ItemList i (is ++ js) ≡ true
  lemma₁ = &&-list₂-t₁ helper₁ helper₂ lemma₀

  lemma₂ : ordList (is ++ js) ≡ true
  lemma₂ = &&-list₂-t₂ helper₁ helper₂ lemma₀

x≤ys→x≤zs→x≤ys++zs : ∀ {i js ks} → N i → ListN js → ListN ks →
                     ≤-ItemList i js →
                     ≤-ItemList i ks →
                     ≤-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni lnnil LNks _ i≤k =
  subst (λ t → ≤-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (lncons {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  le-ItemList i ((j ∷ js) ++ ks)
    ≡⟨ subst (λ t → le-ItemList i ((j ∷ js) ++ ks) ≡
                    le-ItemList i t)
             (++-∷ j js ks)
             refl
    ⟩
  le-ItemList i (j ∷ (js ++ ks))
    ≡⟨ le-ItemList-∷ i j (js ++ ks) ⟩
  le i j && le-ItemList i (js ++ ks)
    ≡⟨ subst₂ (λ t₁ t₂ → le i j && le-ItemList i (js ++ ks) ≡ t₁ && t₂)
              (&&-list₂-t₁ helper₁ helper₂ helper₃)
              (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks
                                  (&&-list₂-t₂ helper₁ helper₂ helper₃)
                                  i≤k)
              refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
  where
  helper₁ : Bool (le i j)
  helper₁ = le-Bool Ni Nj

  helper₂ : Bool (le-ItemList i js)
  helper₂ = le-ItemList-Bool Ni LNjs

  helper₃ : le i j && (le-ItemList i js) ≡ true
  helper₃ = trans (sym (le-ItemList-∷ i j js)) i≤j∷js

xs≤ys→xs≤zs→xs≤ys++zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        ≤-Lists is js →
                        ≤-Lists is ks →
                        ≤-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs lnnil LNjs LNks _ _ = le-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (lncons {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  le-Lists (i ∷ is) (js ++ ks)
    ≡⟨ le-Lists-∷ i is (js ++ ks)  ⟩
  le-ItemList i (js ++ ks) && le-Lists is (js ++ ks)
    ≡⟨ subst (λ t → le-ItemList i (js ++ ks) && le-Lists is (js ++ ks) ≡
                    t                       && le-Lists is (js ++ ks))
             (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks
                                 (&&-list₂-t₁ helper₁ helper₂ helper₃)
                                 (&&-list₂-t₁ helper₄ helper₅ helper₆))
             refl
    ⟩
  true && le-Lists is (js ++ ks)
    ≡⟨ subst (λ t → true && le-Lists is (js ++ ks) ≡ true && t)
             (xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                                    (&&-list₂-t₂ helper₁ helper₂ helper₃)
                                    (&&-list₂-t₂ helper₄ helper₅ helper₆))
             refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
  where
  helper₁ = le-ItemList-Bool Ni LNjs
  helper₂ = le-Lists-Bool LNis LNjs
  helper₃ = trans (sym (le-Lists-∷ i is js)) i∷is≤js

  helper₄ = le-ItemList-Bool Ni LNks
  helper₅ = le-Lists-Bool LNis LNks
  helper₆ = trans (sym (le-Lists-∷ i is ks)) i∷is≤ks

xs≤zs→ys≤zs→xs++ys≤zs : ∀ {is js ks} → ListN is → ListN js → ListN ks →
                        ≤-Lists is ks →
                        ≤-Lists js ks →
                        ≤-Lists (is ++ js) ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks} lnnil LNjs LNks is≤ks js≤ks =
  subst (λ t → ≤-Lists t ks)
        (sym (++-[] js))
        js≤ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks}
                      (lncons {i} {is} Ni LNis) LNjs LNks i∷is≤ks js≤ks =
  le-Lists ((i ∷ is) ++ js) ks
    ≡⟨ subst (λ t → le-Lists ((i ∷ is) ++ js) ks ≡ le-Lists t ks)
             (++-∷ i is js)
             refl
    ⟩
    le-Lists (i ∷ (is ++ js)) ks
    ≡⟨ le-Lists-∷ i (is ++ js) ks ⟩
  le-ItemList i ks && le-Lists (is ++ js) ks
    ≡⟨ subst₂ (λ x y → le-ItemList i ks && le-Lists (is ++ js) ks ≡ x && y)
              ≤-ItemList-i-ks
              ≤-Lists-is++js-ks
              refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎
  where
  helper₁ = le-ItemList-Bool Ni LNks
  helper₂ = le-Lists-Bool LNis LNks
  helper₃ = trans (sym (le-Lists-∷ i is ks)) i∷is≤ks

  ≤-ItemList-i-ks : ≤-ItemList i ks
  ≤-ItemList-i-ks = &&-list₂-t₁ helper₁ helper₂ helper₃

  ≤-Lists-is++js-ks : ≤-Lists (is ++ js) ks
  ≤-Lists-is++js-ks =
    xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks
                          (&&-list₂-t₂ helper₁ helper₂ helper₃)
                          js≤ks
