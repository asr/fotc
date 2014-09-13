------------------------------------------------------------------------------
-- Totality properties for Forest
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Mirror.Forest.TotalityI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

++-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (xs ++ ys)
++-Forest {ys = ys} fnil Fys = subst Forest (sym (++-[] ys)) Fys
++-Forest {ys = ys} (fcons {x} {xs} Tx Fxs) Fys =
  subst Forest (sym (++-∷ x xs ys)) (fcons Tx (++-Forest Fxs Fys))

map-Forest : ∀ {xs} f → (∀ {x} → Tree x → Tree (f · x)) →
             Forest xs → Forest (map f xs)
map-Forest f fTree fnil = subst Forest (sym (map-[] f)) fnil
map-Forest f fTree (fcons {x} {xs} Tx Fxs) =
  subst Forest
        (sym (map-∷ f x xs))
        (fcons (fTree Tx) (map-Forest f fTree Fxs))

rev-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (rev xs ys)
rev-Forest {ys = ys} fnil Fys = subst Forest (sym (rev-[] ys)) Fys
rev-Forest {ys = ys} (fcons {x} {xs} Tx Fxs) Fys =
  subst Forest (sym (rev-∷ x xs ys)) (rev-Forest Fxs (fcons Tx Fys))

reverse-Forest : ∀ {xs} → Forest xs → Forest (reverse xs)
reverse-Forest Fxs = rev-Forest Fxs fnil
