------------------------------------------------------------------------------
-- Properties related with the forest type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Forest.PropertiesATP where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesATP using ( ∷-rightCong )
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesATP
  using ( ++-leftIdentity
        ; mapCong₂
        ; ++-leftCong
        ; reverse-[x]≡[x]
        )
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

++-rightIdentity : ∀ {xs} → Forest xs → xs ++ [] ≡ xs
++-rightIdentity fnil = ++-leftIdentity []
++-rightIdentity (fcons {x} {xs} Tx Fxs) =
  prf (++-rightIdentity Fxs)
  where postulate prf : xs ++ [] ≡ xs → (x ∷ xs) ++ [] ≡ x ∷ xs
        {-# ATP prove prf #-}

++-assoc : ∀ {xs} → Forest xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc fnil ys zs = prf
  where postulate prf : ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs
        {-# ATP prove prf #-}

++-assoc (fcons {x} {xs} Tx Fxs) ys zs = prf (++-assoc Fxs ys zs)
  where postulate prf : (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs →
                        ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs
        {-# ATP prove prf #-}

-- We don't use an automatic proof, because it is necessary to erase a
-- proof term which we don't know how to erase.
map-++ : ∀ f {xs} → (∀ {x} → Tree x → Tree (f · x)) →
         Forest xs →
         ∀ ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f h fnil ys =
  map f ([] ++ ys)
    ≡⟨ mapCong₂ (++-leftIdentity ys) ⟩
  map f ys
    ≡⟨ sym (++-leftIdentity (map f ys)) ⟩
  [] ++ map f ys
     ≡⟨ ++-leftCong (sym (map-[] f)) ⟩
  map f [] ++ map f ys ∎

map-++ f h (fcons {x} {xs} Tx Fxs) ys =
  map f ((x ∷ xs) ++ ys)
    ≡⟨ mapCong₂ (++-∷ x xs ys) ⟩
  map f (x ∷ xs ++ ys)
    ≡⟨ map-∷ f x (xs ++ ys) ⟩
  f · x ∷ map f (xs ++ ys)
    ≡⟨ ∷-rightCong (map-++ f h Fxs ys) ⟩
  f · x ∷ (map f xs ++ map f ys)
    ≡⟨ sym (++-∷ (f · x) (map f xs) (map f ys)) ⟩
  (f · x ∷ map f xs) ++ map f ys
     ≡⟨ ++-leftCong (sym (map-∷ f x xs)) ⟩
  map f (x ∷ xs) ++ map f ys ∎

rev-++ : ∀ {xs} → Forest xs → ∀ ys → rev xs ys ≡ rev xs [] ++ ys
rev-++ fnil ys = prf
  where postulate prf : rev [] ys ≡ rev [] [] ++ ys
        {-# ATP prove prf #-}

rev-++ (fcons {x} {xs} Tx Fxs) ys =
  prf (rev-++ Fxs (x ∷ ys))
      (rev-++ Fxs (x ∷ []))
  where postulate prf : rev xs (x ∷ ys) ≡ rev xs [] ++ x ∷ ys →
                        rev xs (x ∷ []) ≡ rev xs [] ++ x ∷ [] →
                        rev (x ∷ xs) ys ≡ rev (x ∷ xs) [] ++ ys
        {-# ATP prove prf ++-assoc rev-Forest #-}

reverse-++ : ∀ {xs ys} → Forest xs → Forest ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} fnil Fys = prf
  where postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
        {-# ATP prove prf ++-rightIdentity reverse-Forest #-}

reverse-++ (fcons {x} {xs} Tx Fxs) fnil = prf
  where
  postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
  {-# ATP prove prf ++-rightIdentity #-}

reverse-++ (fcons {x} {xs} Tx Fxs) (fcons {y} {ys} Ty Fys) =
  prf (reverse-++ Fxs (fcons Ty Fys))
  where
  postulate prf : reverse (xs ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                           reverse xs →
                  reverse ((x ∷ xs) ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                                 reverse (x ∷ xs)
  {-# ATP prove prf reverse-Forest ++-Forest rev-++ ++-assoc #-}

reverse-∷ : ∀ {x ys} → Tree x → Forest ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ {x} Tx fnil = prf
  where postulate prf : reverse (x ∷ []) ≡ reverse [] ++ x ∷ []
        {-# ATP prove prf #-}

reverse-∷ {x} Tx (fcons {y} {ys} Ty Fys) = prf
  where postulate prf : reverse (x ∷ y ∷ ys) ≡ reverse (y ∷ ys) ++ x ∷ []
        {-# ATP prove prf reverse-[x]≡[x] reverse-++ #-}
