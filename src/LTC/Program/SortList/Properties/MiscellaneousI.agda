------------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.MiscellaneousI where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Bool
  using ( _&&_ ; &&-tt
        ; Bool  -- The LTC booleans type.
        )
open import LTC.Data.Bool.PropertiesI using ( &&-proj₁ ; &&-proj₂ ; ≤-Bool )
open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.List.PropertiesI using ( ++-ListN )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( _++_ ; ++-[] ; ++-∷ )

open import LTC.Program.SortList.Properties.Closures.BoolI
  using ( ≤-ItemList-Bool
        ; ≤-Lists-Bool
        ; ordList-Bool
        )
open import LTC.Program.SortList.SortList

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
-- xs≤[] : {is : D} → ListN is → OrdList is → LE-Lists is []
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

x≤ys++zs→x≤zs : {i js ks : D} → N i → ListN js → ListN ks →
                LE-ItemList i (js ++ ks) → LE-ItemList i ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni nilLN LNks  i≤[]++ks =
  subst (λ t → LE-ItemList i t) (++-[] ks) i≤[]++ks
x≤ys++zs→x≤zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js++ks =
  x≤ys++zs→x≤zs Ni LNjs LNks lemma₂
  where
    lemma₁ : i ≤ j && ≤-ItemList i (js ++ ks) ≡ true
    lemma₁ =
      begin
        i ≤ j && ≤-ItemList i (js ++ ks)
          ≡⟨ sym (≤-ItemList-∷ i j (js ++ ks)) ⟩
        ≤-ItemList i (j ∷ (js ++ ks))
          ≡⟨ subst (λ t → ≤-ItemList i (j ∷ (js ++ ks)) ≡ ≤-ItemList i t )
                   (sym (++-∷ j js ks))
                   refl
          ⟩
        ≤-ItemList i ((j ∷ js) ++ ks) ≡⟨ i≤j∷js++ks ⟩
        true
      ∎

    lemma₂ : LE-ItemList i (js ++ ks)
    lemma₂ = &&-proj₂ (≤-Bool Ni Nj)
                      (≤-ItemList-Bool Ni (++-ListN LNjs LNks))
                      lemma₁

xs++ys-OrdList→xs≤ys : {is js : D} → ListN is → ListN js →
                       OrdList (is ++ js) → LE-Lists is js
xs++ys-OrdList→xs≤ys {js = js} nilLN LNjs OLis++js =  ≤-Lists-[] js
xs++ys-OrdList→xs≤ys {js = js} (consLN {i} {is} Ni LNis) LNjs OLis++js =
  begin
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
    true
  ∎
  where
    lemma₀ : ≤-ItemList i (is ++ js) && ordList (is ++ js) ≡ true
    lemma₀ = trans (sym (ordList-∷ i (is ++ js)))
                   (trans (subst (λ t → ordList (i ∷ is ++ js) ≡ ordList t)
                                 (sym (++-∷ i is js))
                                 refl)
                   OLis++js)

    aux₁ : Bool (≤-ItemList i (is ++ js))
    aux₁ = ≤-ItemList-Bool Ni (++-ListN LNis LNjs)

    aux₂ : Bool (ordList (is ++ js))
    aux₂ = ordList-Bool (++-ListN LNis LNjs)

    lemma₁ : ≤-ItemList i (is ++ js) ≡ true
    lemma₁ = &&-proj₁ aux₁ aux₂ lemma₀

    lemma₂ : ordList (is ++ js) ≡ true
    lemma₂ = &&-proj₂ aux₁ aux₂ lemma₀

x≤ys→x≤zs→x≤ys++zs : {i js ks : D} → N i → ListN js → ListN ks →
                     LE-ItemList i js →
                     LE-ItemList i ks →
                     LE-ItemList i (js ++ ks)
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni nilLN LNks _ i≤k =
  subst (λ t → LE-ItemList i t) (sym (++-[] ks)) i≤k
x≤ys→x≤zs→x≤ys++zs {i} {ks = ks} Ni (consLN {j} {js} Nj LNjs) LNks i≤j∷js i≤k =
  begin
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
                (&&-proj₁ aux₁ aux₂ aux₃)
                -- IH.
                (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks (&&-proj₂ aux₁ aux₂ aux₃) i≤k)
                refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎
  where
    aux₁ : Bool (i ≤ j)
    aux₁ = ≤-Bool Ni Nj

    aux₂ : Bool (≤-ItemList i js)
    aux₂ = ≤-ItemList-Bool Ni LNjs

    aux₃ : i ≤ j && (≤-ItemList i js) ≡ true
    aux₃ = trans (sym (≤-ItemList-∷ i j js)) i≤j∷js

xs≤ys→xs≤zs→xs≤ys++zs : {is js ks : D} → ListN is → ListN js → ListN ks →
                        LE-Lists is js →
                        LE-Lists is ks →
                        LE-Lists is (js ++ ks)
xs≤ys→xs≤zs→xs≤ys++zs nilLN LNjs LNks _ _ = ≤-Lists-[] _
xs≤ys→xs≤zs→xs≤ys++zs {js = js} {ks} (consLN {i} {is} Ni LNis)
                      LNjs LNks i∷is≤js i∷is≤ks =
  begin
    ≤-Lists (i ∷ is) (js ++ ks)
      ≡⟨ ≤-Lists-∷ i is (js ++ ks)  ⟩
    ≤-ItemList i (js ++ ks) && ≤-Lists is (js ++ ks)
      ≡⟨ subst (λ t → ≤-ItemList i (js ++ ks) && ≤-Lists is (js ++ ks) ≡
                      t                       && ≤-Lists is (js ++ ks))
               (x≤ys→x≤zs→x≤ys++zs Ni LNjs LNks
                                   (&&-proj₁ aux₁ aux₂ aux₃)
                                   (&&-proj₁ aux₄ aux₅ aux₆))
               refl
      ⟩
    true && ≤-Lists is (js ++ ks)
      ≡⟨ subst (λ t → true && ≤-Lists is (js ++ ks) ≡ true && t)
               -- IH.
               (xs≤ys→xs≤zs→xs≤ys++zs LNis LNjs LNks
                                      (&&-proj₂ aux₁ aux₂ aux₃)
                                      (&&-proj₂ aux₄ aux₅ aux₆))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎
  where
    aux₁ = ≤-ItemList-Bool Ni LNjs
    aux₂ = ≤-Lists-Bool LNis LNjs
    aux₃ = trans (sym (≤-Lists-∷ i is js)) i∷is≤js

    aux₄ = ≤-ItemList-Bool Ni LNks
    aux₅ = ≤-Lists-Bool LNis LNks
    aux₆ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

xs≤zs→ys≤zs→xs++ys≤zs : {is js ks : D} → ListN is → ListN js → ListN ks →
                        LE-Lists is ks →
                        LE-Lists js ks →
                        LE-Lists (is ++ js) ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks} nilLN LNjs LNks is≤ks js≤ks =
  subst (λ t → LE-Lists t ks)
        (sym (++-[] js))
        js≤ks
xs≤zs→ys≤zs→xs++ys≤zs {js = js} {ks}
                      (consLN {i} {is} Ni LNis) LNjs LNks i∷is≤ks js≤ks =
  begin
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
    true
  ∎
  where
    aux₁ = ≤-ItemList-Bool Ni LNks
    aux₂ = ≤-Lists-Bool LNis LNks
    aux₃ = trans (sym (≤-Lists-∷ i is ks)) i∷is≤ks

    LE-ItemList-i-ks : LE-ItemList i ks
    LE-ItemList-i-ks = &&-proj₁ aux₁ aux₂ aux₃

    -- IH.
    LE-Lists-is++js-ks : LE-Lists (is ++ js) ks
    LE-Lists-is++js-ks =
      xs≤zs→ys≤zs→xs++ys≤zs LNis LNjs LNks (&&-proj₂ aux₁ aux₂ aux₃) js≤ks
