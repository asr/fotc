------------------------------------------------------------------------------
-- Properties for the relation LTC
------------------------------------------------------------------------------

module FOTC.Data.List.LT-Cons.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.List
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.LT-Cons
open import FOTC.Data.List.PropertiesI

------------------------------------------------------------------------------

-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → List ys → LTC xs ys → LTL xs ys
LTC→LTL Lxs _ (x , ys≡x∷xs) = helper Lxs ys≡x∷xs
  where
  helper : ∀ {x xs ys} → List xs → ys ≡ x ∷ xs → LT (length xs) (length ys)
  helper {x} Lxs refl = lg-x<lg-x∷xs x Lxs
