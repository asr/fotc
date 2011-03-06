------------------------------------------------------------------------------
-- Properties related with the forest type
------------------------------------------------------------------------------

module FOTC.Program.Mirror.Forest.PropertiesATP where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI using (reverse-[x]≡[x])

open import FOTC.Program.Mirror.Forest.Closures
open import FOTC.Program.Mirror.Type

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

++-leftIdentity : ∀ {xs} → Forest xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → Forest xs → xs ++ [] ≡ xs
++-rightIdentity nilF                     = ++-[] []
++-rightIdentity (consF {x} {xs} Tx Fxs) = prf (++-rightIdentity Fxs)
  where
    postulate prf : xs ++ [] ≡ xs →
                    (x ∷ xs) ++ [] ≡ x ∷ xs
    {-# ATP prove prf #-}

++-assoc : ∀ {xs ys zs} → Forest xs → Forest ys → Forest zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {ys = ys} {zs} nilF Fys Fzs = prf
  where
    postulate prf : ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs
    {-# ATP prove prf #-}

++-assoc {ys = ys} {zs} (consF {x} {xs} Tx Fxs) Fys Fzs =
  prf (++-assoc Fxs Fys Fzs)
  where
    postulate prf : (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs → -- IH.
                    ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs
    {-# ATP prove prf #-}

rev-++-commute : ∀ {xs ys} → Forest xs → Forest ys →
                 rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilF Fys = prf
  where
    postulate prf : rev [] ys ≡ rev [] [] ++ ys
    {-# ATP prove prf #-}

rev-++-commute {ys = ys} (consF {x} {xs} Tx Fxs) Fys =
  prf (rev-++-commute Fxs (consF Tx Fys))
      (rev-++-commute Fxs (consF Tx nilF))
  where
    postulate prf : rev xs (x ∷ ys) ≡ rev xs [] ++ x ∷ ys →  -- IH.
                    rev xs (x ∷ []) ≡ rev xs [] ++ x ∷ [] →  -- IH.
                    rev (x ∷ xs) ys ≡ rev (x ∷ xs) [] ++ ys
    {-# ATP prove prf ++-assoc rev-Forest ++-Forest #-}

reverse-++-commute : ∀ {xs ys} → Forest xs → Forest ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} nilF Fys = prf
  where
    postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-Forest #-}

reverse-++-commute (consF {x} {xs} Tx Fxs) nilF = prf
  where
    postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
    {-# ATP prove prf ++-rightIdentity #-}

reverse-++-commute (consF {x} {xs} Tx Fxs) (consF {y} {ys} Ty Fys) =
  prf $ reverse-++-commute Fxs (consF Ty Fys)
  where
    postulate prf : reverse (xs ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                             reverse xs →  -- IH.
                    reverse ((x ∷ xs) ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                                   reverse (x ∷ xs)
    {-# ATP prove prf reverse-Forest ++-Forest rev-++-commute ++-assoc #-}

reverse-∷ : ∀ {x ys} → Tree x → Forest ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ {x} Tx nilF = prf
  where
    postulate prf : reverse (x ∷ []) ≡ reverse [] ++ x ∷ []
    {-# ATP prove prf ++-leftIdentity #-}

reverse-∷ {x} Tx (consF {y} {ys} Ty Fys) = prf
  where
    postulate prf : reverse (x ∷ y ∷ ys) ≡ reverse (y ∷ ys) ++ x ∷ []
    {-# ATP prove prf reverse-[x]≡[x] reverse-++-commute ++-leftIdentity #-}

map-++-commute : ∀ f {xs ys} → (∀ {x} → Tree x → Tree (f · x)) →
                 Forest xs → Forest ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f {ys = ys} fTree nilF Fys =
  begin
    map f ([] ++ ys)
      ≡⟨ subst (λ t → map f ([] ++ ys) ≡ map f t)
               (++-[] ys)
               refl
      ⟩
    map f ys
      ≡⟨ sym (++-leftIdentity (map-Forest f fTree Fys)) ⟩
    [] ++ map f ys
      ≡⟨ subst (λ t → [] ++ map f ys ≡ t ++ map f ys)
               (sym (map-[] f))
               refl
      ⟩
    map f [] ++ map f ys
  ∎

map-++-commute f {ys = ys} fTree (consF {x} {xs} Tx Fxs) Fys =
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
               (map-++-commute f fTree Fxs Fys) -- IH.
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
