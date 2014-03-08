------------------------------------------------------------------------------
-- Properties related with the forest type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Forest.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Program.Mirror.Forest.TotalityI
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

++-rightIdentity-forest : ∀ {xs} → Forest xs → xs ++ [] ≡ xs
++-rightIdentity-forest fnil                    = ++-leftIdentity []
++-rightIdentity-forest (fcons {x} {xs} Tx Fxs) =
  (x ∷ xs) ++ []
     ≡⟨ ++-∷ x xs [] ⟩
  x ∷ (xs ++ [])
    ≡⟨ ∷-rightCong (++-rightIdentity-forest Fxs) ⟩
  x ∷ xs ∎

++-assoc-forest :
  ∀ {xs} → Forest xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc-forest fnil ys zs =
  ([] ++ ys) ++ zs
    ≡⟨ ++-leftCong (++-leftIdentity ys) ⟩
  ys ++ zs
     ≡⟨ sym (++-leftIdentity (ys ++ zs)) ⟩
  [] ++ ys ++ zs ∎

++-assoc-forest (fcons {x} {xs} Tx Fxs) ys zs =
  ((x ∷ xs) ++ ys) ++ zs
    ≡⟨ ++-leftCong (++-∷ x xs ys) ⟩
  (x ∷ (xs ++ ys)) ++ zs
     ≡⟨ ++-∷ x (xs ++ ys) zs ⟩
  x ∷ ((xs ++ ys) ++ zs)
    ≡⟨ ∷-rightCong (++-assoc-forest Fxs ys zs) ⟩
  x ∷ (xs ++ ys ++ zs)
    ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
  (x ∷ xs) ++ ys ++ zs ∎

map-++-forest : ∀ f {xs} → (∀ {x} → Tree x → Tree (f · x)) →
                Forest xs → ∀ ys →
                map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-forest f h fnil ys =
  map f ([] ++ ys)
    ≡⟨ mapCong₂ (++-leftIdentity ys) ⟩
  map f ys
    ≡⟨ sym (++-leftIdentity (map f ys)) ⟩
  [] ++ map f ys
     ≡⟨ ++-leftCong (sym (map-[] f)) ⟩
  map f [] ++ map f ys ∎

map-++-forest f h (fcons {x} {xs} Tx Fxs) ys =
  map f ((x ∷ xs) ++ ys)
    ≡⟨ mapCong₂ (++-∷ x xs ys) ⟩
  map f (x ∷ xs ++ ys)
    ≡⟨ map-∷ f x (xs ++ ys) ⟩
  f · x ∷ map f (xs ++ ys)
    ≡⟨ ∷-rightCong (map-++-forest f h Fxs ys) ⟩
  f · x ∷ (map f xs ++ map f ys)
    ≡⟨ sym (++-∷ (f · x) (map f xs) (map f ys)) ⟩
  (f · x ∷ map f xs) ++ map f ys
     ≡⟨ ++-leftCong (sym (map-∷ f x xs)) ⟩
  map f (x ∷ xs) ++ map f ys ∎

rev-++-forest : ∀ {xs} → Forest xs → ∀ ys → rev xs ys ≡ rev xs [] ++ ys
rev-++-forest fnil ys =
  rev [] ys       ≡⟨ rev-[] ys ⟩
  ys              ≡⟨ sym (++-leftIdentity ys) ⟩
  [] ++ ys        ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  rev [] [] ++ ys ∎

rev-++-forest (fcons {x} {xs} Tx Fxs) ys =
  rev (x ∷ xs) ys
    ≡⟨ rev-∷ x xs ys ⟩
  rev xs (x ∷ ys)
    ≡⟨ rev-++-forest Fxs (x ∷ ys) ⟩
  rev xs [] ++ x ∷ ys
    ≡⟨ ++-rightCong prf ⟩
  rev xs [] ++ (x ∷ []) ++ ys
    ≡⟨ sym (++-assoc-forest (rev-Forest Fxs fnil) (x ∷ []) ys) ⟩
  (rev xs [] ++ (x ∷ [])) ++ ys
    ≡⟨ ++-leftCong (sym (rev-++-forest Fxs (x ∷ []))) ⟩
  rev xs (x ∷ []) ++ ys
    ≡⟨ ++-leftCong (sym (rev-∷ x xs [])) ⟩
  rev (x ∷ xs) [] ++ ys ∎
    where prf : x ∷ ys ≡ (x ∷ []) ++ ys
          prf = x ∷ ys         ≡⟨ ∷-rightCong (sym (++-leftIdentity ys)) ⟩
                x ∷ ([] ++ ys) ≡⟨ sym (++-∷ x [] ys) ⟩
                (x ∷ []) ++ ys ∎

reverse-++-forest : ∀ {xs ys} → Forest xs → Forest ys →
                    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-forest {ys = ys} fnil Fys =
  reverse ([] ++ ys)
    ≡⟨ reverseCong (++-leftIdentity ys) ⟩
  reverse ys
    ≡⟨ sym (++-rightIdentity-forest (reverse-Forest Fys)) ⟩
  reverse ys ++ []
    ≡⟨ ++-rightCong (sym (rev-[] [])) ⟩
  reverse ys ++ reverse [] ∎

reverse-++-forest (fcons {x} {xs} Tx Fxs) fnil =
  reverse ((x ∷ xs) ++ [])
    ≡⟨ reverseCong (++-rightIdentity-forest (fcons Tx Fxs)) ⟩
  reverse (x ∷ xs)
    ≡⟨ sym (++-leftIdentity (reverse (x ∷ xs))) ⟩
  [] ++ reverse (x ∷ xs)
     ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  reverse [] ++ reverse (x ∷ xs) ∎

reverse-++-forest (fcons {x} {xs} Tx Fxs) (fcons {y} {ys} Ty Fys) =
  rev ((x ∷ xs) ++ y ∷ ys) []
    ≡⟨ revCong₁ (++-∷ x xs (y ∷ ys)) ⟩
  rev (x ∷ (xs ++ y ∷ ys)) []
    ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
  rev (xs ++ y ∷ ys) (x ∷ [])
    ≡⟨ rev-++-forest (++-Forest Fxs (fcons Ty Fys)) (x ∷ []) ⟩
  rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
    ≡⟨ ++-leftCong refl ⟩
  reverse (xs ++ y ∷ ys) ++ (x ∷ [])
    ≡⟨ ++-leftCong (reverse-++-forest Fxs (fcons Ty Fys)) ⟩
  (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
    ≡⟨ ++-assoc-forest (reverse-Forest (fcons Ty Fys))
                       (reverse xs)
                       (x ∷ [])
    ⟩
  reverse (y ∷ ys) ++ rev xs [] ++ x ∷ []
    ≡⟨ ++-rightCong (sym (rev-++-forest Fxs (x ∷ []))) ⟩
  reverse (y ∷ ys) ++ rev xs (x ∷ [])
    ≡⟨ ++-rightCong (sym (rev-∷ x xs [])) ⟩
  reverse (y ∷ ys) ++ reverse (x ∷ xs) ∎

reverse-∷-forest : ∀ {x ys} → Tree x → Forest ys →
                   reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷-forest {x} Tx fnil =
  rev (x ∷ []) []
    ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ [])
    ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []
    ≡⟨ sym (++-leftIdentity (x ∷ [])) ⟩
  [] ++ x ∷ []
     ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  rev [] [] ++ x ∷ [] ∎

reverse-∷-forest {x} Tx (fcons {y} {ys} Ty Fys) = sym (
  reverse (y ∷ ys) ++ x ∷ []
    ≡⟨ ++-rightCong (sym (reverse-[x]≡[x] x)) ⟩
  (reverse (y ∷ ys) ++ reverse (x ∷ []))
    ≡⟨ sym (reverse-++-forest (fcons Tx fnil) (fcons Ty Fys)) ⟩
  reverse ((x ∷ []) ++ (y ∷ ys))
     ≡⟨ reverseCong (++-∷ x [] (y ∷ ys)) ⟩
   reverse (x ∷ ([] ++ (y ∷ ys)))
     ≡⟨ reverseCong (∷-rightCong (++-leftIdentity (y ∷ ys))) ⟩
   reverse (x ∷ y ∷ ys) ∎
  )
