------------------------------------------------------------------------------
-- Properties related with the closures of the forest type
------------------------------------------------------------------------------

module FOTC.Program.Mirror.Forest.Closures where

open import FOTC.Base

open import FOTC.Program.Mirror.Type

open import FOTC.Data.List

------------------------------------------------------------------------------

++-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (xs ++ ys)
++-Forest {ys = ys} nilF Fys = subst Forest (sym (++-[] ys)) Fys
++-Forest {ys = ys} (consF {x} {xs} Tx Fxs) Fys =
  subst Forest (sym (++-∷ x xs ys)) (consF Tx (++-Forest Fxs Fys))

map-Forest : ∀ {xs} f → (∀ {x} → Tree x → Tree (f · x)) →
             Forest xs → Forest (map f xs)
map-Forest f fTree nilF = subst Forest (sym (map-[] f)) nilF
map-Forest f fTree (consF {x} {xs} Tx Fxs) =
  subst Forest
        (sym (map-∷ f x xs))
        (consF (fTree Tx) (map-Forest f fTree Fxs))

rev-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (rev xs ys)
rev-Forest {ys = ys} nilF Fys = subst Forest (sym (rev-[] ys)) Fys
rev-Forest {ys = ys} (consF {x} {xs} Tx Fxs) Fys =
  subst Forest (sym (rev-∷ x xs ys)) (rev-Forest Fxs (consF Tx Fys))

reverse-Forest : ∀ {xs} → Forest xs → Forest (reverse xs)
reverse-Forest Fxs = rev-Forest Fxs nilF
