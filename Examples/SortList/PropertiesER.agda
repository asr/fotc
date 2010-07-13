------------------------------------------------------------------------------
-- Miscellaneous properties (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.Closures.BoolER
  using ( ≤-ItemList-Bool ; isListOrd-Bool )
open import Examples.SortList.SortList

open import LTC.Data.Bool
open import LTC.Data.Bool.PropertiesER using
  ( x&&y≡true→x≡true ; x&&y≡true→y≡true )
open import LTC.Data.Nat.List
open import LTC.Data.Nat.Type

import MyStdLib.Relation.Binary.EqReasoning
open module Properties-ER =
  MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------

------------------------------------------------------------------------------

-- If (i ∷ is) is ordered then 'is' is ordered.
-- This function is defined in this module to avoid cyclical dependencies.
subList-ListOrd : {i : D} → N i → {is : D} → List is → ListOrd (i ∷ is) →
                  ListOrd is
subList-ListOrd {i} Ni nilL LOi∷is = isListOrd-[]

subList-ListOrd {i} Ni (consL {j} {js} Nj Ljs) LOi∷j∷js =
  x&&y≡true→y≡true (≤-ItemList-Bool Ni (consL Nj Ljs))
                   (isListOrd-Bool (consL Nj Ljs))
                   (trans (sym (isListOrd-∷ i (j ∷ js))) LOi∷j∷js)

xs≤[] : {is : D} → List is → ListOrd is → LE-Lists is []
xs≤[] nilL _ = ≤-Lists-[] []
xs≤[] (consL {i} {is} Ni Lis) LOconsL =
  begin
    ≤-Lists (i ∷ is) []
      ≡⟨ ≤-Lists-∷ i is [] ⟩
    ≤-ItemList i is && ≤-Lists is []
      ≡⟨ subst (λ t → ≤-ItemList i is && ≤-Lists is [] ≡
                      t && ≤-Lists is [])
               (x&&y≡true→x≡true (≤-ItemList-Bool Ni Lis)
                                 (isListOrd-Bool Lis)
                                 (trans (sym (isListOrd-∷ i is)) LOconsL))
               refl
      ⟩
    true && ≤-Lists is []
      ≡⟨ subst (λ t → true && ≤-Lists is [] ≡ true && t)
               -- IH.
               (xs≤[] Lis (subList-ListOrd Ni Lis LOconsL))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎
