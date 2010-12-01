------------------------------------------------------------------------------
-- Miscellaneous properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Program.SortList.PropertiesER where

open import LTC.Base

open import Common.Function using ( _$_ )
open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

open import LTC.Data.Bool using ( _&&_ ; &&-tt )
open import LTC.Data.Bool.PropertiesER
  using ( x&&y≡true→x≡true
        ; x&&y≡true→y≡true
        )
open import LTC.Data.Nat.List.PropertiesER using ( ++-ListN )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( _++_ ; ++-[] ; ++-∷ )

open import LTC.Program.SortList.Closures.BoolER
  using ( ≤-ItemList-Bool
        ; isListOrd-Bool
        )
open import LTC.Program.SortList.SortList
  using ( ≤-ItemList
        ; ≤-Lists ; ≤-Lists-[] ; ≤-Lists-∷
        ; isListOrd ; isListOrd-[] ; isListOrd-∷
        ; LE-Lists
        ; ListOrd
        )

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
-- This function is defined in this module to avoid cyclical dependencies.
subList-ListOrd : {i : D} → N i → {is : D} → ListN is → ListOrd (i ∷ is) →
                  ListOrd is
subList-ListOrd {i} Ni nilLN LOi∷is = isListOrd-[]

subList-ListOrd {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js =
  x&&y≡true→y≡true (≤-ItemList-Bool Ni (consLN Nj Ljs))
                   (isListOrd-Bool (consLN Nj Ljs))
                   (trans (sym $ isListOrd-∷ i (j ∷ js)) LOi∷j∷js)

-- This is a weird result but recall that "the relation ≤ between
-- lists is only an ordering if nil is excluded" (Burstall, pp. 46).
xs≤[] : {is : D} → ListN is → ListOrd is → LE-Lists is []
xs≤[] nilLN                     _       = ≤-Lists-[] []
xs≤[] (consLN {i} {is} Ni LNis) LOconsL =
  begin
    ≤-Lists (i ∷ is) []
      ≡⟨ ≤-Lists-∷ i is [] ⟩
    ≤-ItemList i is && ≤-Lists is []
      ≡⟨ subst (λ t → ≤-ItemList i is && ≤-Lists is [] ≡
                      t && ≤-Lists is [])
               (x&&y≡true→x≡true (≤-ItemList-Bool Ni LNis)
                                 (isListOrd-Bool LNis)
                                 (trans (sym $ isListOrd-∷ i is) LOconsL))
               refl
      ⟩
    true && ≤-Lists is []
      ≡⟨ subst (λ t → true && ≤-Lists is [] ≡ true && t)
               (xs≤[] LNis (subList-ListOrd Ni LNis LOconsL))  -- IH.
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎

listOrd-xs++ys→ys≤zs→xs++ys≤zs :
  {is js ks : D} → ListN is → ListN js → ListN ks → ListOrd (is ++ js) →
  LE-Lists js ks → LE-Lists (is ++ js) ks

listOrd-xs++ys→ys≤zs→xs++ys≤zs
  {js = js} {ks = ks} nilLN LNjs LNks LOis++js js≤ks =
  trans (subst (λ t → ≤-Lists ([] ++ js) ks ≡ ≤-Lists t ks)
               (++-[] js)
               refl)
        js≤ks

listOrd-xs++ys→ys≤zs→xs++ys≤zs
  {js = js} {ks = ks} (consLN {i} {is} Ni LNis) LNjs LNks LOi∷is++js js≤ks =
  begin
    ≤-Lists ((i ∷ is) ++ js) ks
      ≡⟨ subst (λ t → ≤-Lists ((i ∷ is) ++ js) ks ≡ ≤-Lists t ks)
               (++-∷ i is js)
               refl
      ⟩
    ≤-Lists (i ∷ (is ++ js)) ks
      ≡⟨ ≤-Lists-∷ i (is ++ js) ks ⟩
    ≤-ItemList i (is ++ js) && ≤-Lists (is ++ js) ks
      ≡⟨ subst (λ t → ≤-ItemList i (is ++ js) && ≤-Lists (is ++ js) ks ≡
                      t && ≤-Lists (is ++ js) ks)
               (x&&y≡true→x≡true
                 (≤-ItemList-Bool Ni (++-ListN LNis LNjs))
                 (isListOrd-Bool (++-ListN LNis LNjs))
                 (trans (sym $ isListOrd-∷ i (is ++ js))
                        (trans (subst (λ t → isListOrd (i ∷ is ++ js) ≡
                                             isListOrd t)
                                      (sym $ ++-∷ i is js)
                                      refl)
                               LOi∷is++js)))

               refl
      ⟩
    true && ≤-Lists (is ++ js) ks
      ≡⟨ subst (λ t → true && ≤-Lists (is ++ js) ks ≡ true && t)
               -- IH.
               (listOrd-xs++ys→ys≤zs→xs++ys≤zs LNis LNjs LNks
                 (x&&y≡true→y≡true
                   (≤-ItemList-Bool Ni (++-ListN LNis LNjs))
                   (isListOrd-Bool (++-ListN LNis LNjs))
                   (trans (sym $ isListOrd-∷ i (is ++ js))
                          (trans (subst (λ t → isListOrd (i ∷ is ++ js) ≡
                                               isListOrd t)
                                        (sym $ ++-∷ i is js)
                                        refl)
                                 LOi∷is++js)))
                 js≤ks)
               refl
      ⟩
    true && true ≡⟨ &&-tt ⟩
    true
  ∎
