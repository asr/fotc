------------------------------------------------------------------------------
-- Properties related with the closures of the lists of trees type
------------------------------------------------------------------------------

module LTC.Program.Mirror.ListTree.Closures where

open import LTC.Base

open import LTC.Program.Mirror.Mirror

open import LTC.Data.List

------------------------------------------------------------------------------

++-ListTree : ∀ {xs ys} → ListTree xs → ListTree ys → ListTree (xs ++ ys)
++-ListTree {ys = ys} nilLT LTys = subst ListTree (sym (++-[] ys)) LTys
++-ListTree {ys = ys} (consLT {x} {xs} Tx LTxs) LTys =
  subst ListTree (sym (++-∷ x xs ys)) (consLT Tx (++-ListTree LTxs LTys))

map-ListTree : ∀ {xs} f → (∀ {x} → Tree x → Tree (f · x)) →
               ListTree xs → ListTree (map f xs)
map-ListTree f fTree nilLT = subst ListTree (sym (map-[] f)) nilLT
map-ListTree f fTree (consLT {x} {xs} Tx LTxs) =
  subst ListTree
        (sym (map-∷ f x xs))
        (consLT (fTree Tx) (map-ListTree f fTree LTxs))

rev-ListTree : ∀ {xs ys} → ListTree xs → ListTree ys → ListTree (rev xs ys)
rev-ListTree {ys = ys} nilLT LTys = subst ListTree (sym (rev-[] ys)) LTys
rev-ListTree {ys = ys} (consLT {x} {xs} Tx LTxs) LTys =
  subst ListTree (sym (rev-∷ x xs ys)) (rev-ListTree LTxs (consLT Tx LTys))

reverse-ListTree : ∀ {xs} → ListTree xs → ListTree (reverse xs)
reverse-ListTree LTxs = rev-ListTree LTxs nilLT
