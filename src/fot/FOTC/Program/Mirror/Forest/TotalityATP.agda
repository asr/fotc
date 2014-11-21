------------------------------------------------------------------------------
-- Totality properties for Forest
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Mirror.Forest.TotalityATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

++-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (xs ++ ys)
++-Forest {ys = ys} fnil Fys = prf
  where postulate prf : Forest ([] ++ ys)
        {-# ATP prove prf #-}
++-Forest {ys = ys} (fcons {x} {xs} Tx Fxs) Fys = prf (++-Forest Fxs Fys)
  where postulate prf : Forest (xs ++ ys) →
                        Forest ((x ∷ xs) ++ ys)
        {-# ATP prove prf #-}

-- We don't use a combined proof, because it is necessary to erase a
-- proof term which we don't know how to erase.
map-Forest : ∀ {xs} f → (∀ {x} → Tree x → Tree (f · x)) →
             Forest xs → Forest (map f xs)
map-Forest f fTree fnil = subst Forest (sym (map-[] f)) fnil
map-Forest f fTree (fcons {x} {xs} Tx Fxs) =
  subst Forest
        (sym (map-∷ f x xs))
        (fcons (fTree Tx) (map-Forest f fTree Fxs))

rev-Forest : ∀ {xs ys} → Forest xs → Forest ys → Forest (rev xs ys)
rev-Forest {ys = ys} fnil Fys = prf
  where postulate prf : Forest (rev [] ys)
        {-# ATP prove prf #-}
rev-Forest {ys = ys} (fcons {x} {xs} Tx Fxs) Fys =
  prf (rev-Forest Fxs (fcons Tx Fys))
  where postulate prf : Forest (rev xs (x ∷ ys)) →
                        Forest (rev (x ∷ xs) ys)
        {-# ATP prove prf #-}

postulate reverse-Forest : ∀ {xs} → Forest xs → Forest (reverse xs)
{-# ATP prove reverse-Forest rev-Forest #-}
