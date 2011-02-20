------------------------------------------------------------------------------
-- Properties related with lists of trees
------------------------------------------------------------------------------

module LTC.Program.Mirror.ListTree.PropertiesATP where

open import LTC.Base

open import Common.Function

open import LTC.Data.List
open import LTC.Data.List.PropertiesI using (reverse-[x]≡[x])

open import LTC.Program.Mirror.Mirror
open import LTC.Program.Mirror.ListTree.Closures

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

++-leftIdentity : ∀ {xs} → ListTree xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → ListTree xs → xs ++ [] ≡ xs
++-rightIdentity nilLT               = ++-[] []
++-rightIdentity (consLT {x} {xs} Tx LTxs) = prf (++-rightIdentity LTxs)
  where
    postulate prf :  xs ++ [] ≡ xs →
                    (x ∷ xs) ++ [] ≡ x ∷ xs
    {-# ATP prove prf #-}

++-assoc : ∀ {xs ys zs} → ListTree xs → ListTree ys → ListTree zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {ys = ys} {zs} nilLT LTys LTzs = prf
  where
    postulate prf : ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs
    {-# ATP prove prf #-}

++-assoc {ys = ys} {zs} (consLT {x} {xs} Tx LTxs) LTys LTzs =
  prf (++-assoc LTxs LTys LTzs)
  where
    postulate prf : (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs → -- IH.
                    ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs
    {-# ATP prove prf #-}

rev-++-commute : ∀ {xs ys} → ListTree xs → ListTree ys →
                 rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilLT LTys = prf
  where
    postulate prf : rev [] ys ≡ rev [] [] ++ ys
    {-# ATP prove prf #-}

rev-++-commute {ys = ys} (consLT {x} {xs} Tx LTxs) LTys =
  prf (rev-++-commute LTxs (consLT Tx LTys))
      (rev-++-commute LTxs (consLT Tx nilLT))
  where
    postulate prf : rev xs (x ∷ ys) ≡ rev xs [] ++ x ∷ ys →  -- IH.
                    rev xs (x ∷ []) ≡ rev xs [] ++ x ∷ [] →  -- IH.
                    rev (x ∷ xs) ys ≡ rev (x ∷ xs) [] ++ ys
    {-# ATP prove prf ++-assoc rev-ListTree ++-ListTree #-}

reverse-++-commute : ∀ {xs ys} → ListTree xs → ListTree ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} nilLT LTys = prf
  where
    postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-ListTree #-}

reverse-++-commute (consLT {x} {xs} Tx LTxs) nilLT = prf
  where
    postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
    {-# ATP prove prf ++-rightIdentity #-}

reverse-++-commute (consLT {x} {xs} Tx LTxs) (consLT {y} {ys} Ty LTys) =
  prf $ reverse-++-commute LTxs (consLT Ty LTys)
  where
    postulate prf : reverse (xs ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                             reverse xs →  -- IH.
                    reverse ((x ∷ xs) ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                                   reverse (x ∷ xs)
    {-# ATP prove prf reverse-ListTree ++-ListTree rev-++-commute ++-assoc #-}

reverse-∷ : ∀ {x ys} → Tree x → ListTree ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ {x} Tx nilLT = prf
  where
    postulate prf : reverse (x ∷ []) ≡ reverse [] ++ x ∷ []
    {-# ATP prove prf ++-leftIdentity #-}

reverse-∷ {x} Tx (consLT {y} {ys} Ty LTys) = prf
  where
    postulate prf : reverse (x ∷ y ∷ ys) ≡ reverse (y ∷ ys) ++ x ∷ []
    {-# ATP prove prf reverse-[x]≡[x] reverse-++-commute ++-leftIdentity #-}

map-++-commute : ∀ f {xs ys} → (∀ {x} → Tree x → Tree (f · x)) →
                 ListTree xs → ListTree ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f {ys = ys} fTree nilLT LTys =
  begin
    map f ([] ++ ys)
      ≡⟨ subst (λ t → map f ([] ++ ys) ≡ map f t)
               (++-[] ys)
               refl
      ⟩
    map f ys
      ≡⟨ sym (++-leftIdentity (map-ListTree f fTree LTys)) ⟩
    [] ++ map f ys
      ≡⟨ subst (λ t → [] ++ map f ys ≡ t ++ map f ys)
               (sym (map-[] f))
               refl
      ⟩
    map f [] ++ map f ys
  ∎

map-++-commute f {ys = ys} fTree (consLT {x} {xs} Tx LTxs) LTys =
  begin
    map f ((x ∷ xs) ++ ys)
      ≡⟨ subst (λ t → map f ((x ∷ xs) ++ ys) ≡ map f t)
               (++-∷ x xs ys)
               refl
      ⟩
    map f (x ∷ xs ++ ys)
      ≡⟨ map-∷ f x (xs ++ ys) ⟩
    f · x ∷ map f (xs ++ ys)
      ≡⟨ subst (λ t → f · x ∷ map f (xs ++ ys) ≡ f · x ∷ t)
               (map-++-commute f fTree LTxs LTys) -- IH.
               refl
      ⟩
    f · x ∷ (map f xs ++ map f ys)
      ≡⟨ sym (++-∷ (f · x) (map f xs) (map f ys)) ⟩
    (f · x ∷ map f xs) ++ map f ys
      ≡⟨ subst (λ t → (f · x ∷ map f xs) ++ map f ys ≡ t ++ map f ys)
               (sym (map-∷ f x xs))
               refl
      ⟩
    map f (x ∷ xs) ++ map f ys
  ∎
