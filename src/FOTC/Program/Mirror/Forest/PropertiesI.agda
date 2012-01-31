------------------------------------------------------------------------------
-- Properties related with the forest type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Forest.PropertiesI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI using (reverse-[x]≡[x])
open import FOTC.Program.Mirror.Forest.Totality
open import FOTC.Program.Mirror.Type
open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

++-leftIdentity : ∀ {xs} → Forest xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → Forest xs → xs ++ [] ≡ xs
++-rightIdentity nilF                     = ++-[] []
++-rightIdentity (consF {x} {xs} Tx Fxs) =
  (x ∷ xs) ++ []
     ≡⟨ ++-∷ x xs [] ⟩
  x ∷ (xs ++ [])
    ≡⟨ subst (λ t → x ∷ (xs ++ []) ≡ x ∷ t)
             (++-rightIdentity Fxs) -- IH.
             refl
    ⟩
  x ∷ xs ∎

++-assoc : ∀ {xs ys zs} → Forest xs → Forest ys → Forest zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {ys = ys} {zs} nilF Fys Fzs =
  ([] ++ ys) ++ zs
    ≡⟨ subst (λ t → ([] ++ ys) ++ zs ≡ t ++ zs)
             (++-[] ys)
             refl
    ⟩
  ys ++ zs
     ≡⟨ sym (++-leftIdentity (++-Forest Fys Fzs)) ⟩
  [] ++ ys ++ zs ∎

++-assoc {ys = ys} {zs} (consF {x} {xs} Tx Fxs) Fys Fzs =
  ((x ∷ xs) ++ ys) ++ zs
    ≡⟨ subst (λ t → ((x ∷ xs) ++ ys) ++ zs ≡ t ++ zs)
             (++-∷ x xs ys)
             refl
    ⟩
  (x ∷ (xs ++ ys)) ++ zs
     ≡⟨ ++-∷ x (xs ++ ys) zs ⟩
  x ∷ ((xs ++ ys) ++ zs)
    ≡⟨ subst (λ t → x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ t)
             (++-assoc Fxs Fys Fzs) -- IH.
             refl
    ⟩
  x ∷ (xs ++ ys ++ zs)
    ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
  (x ∷ xs) ++ ys ++ zs ∎

rev-++-commute : ∀ {xs ys} → Forest xs → Forest ys →
                 rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilF Fys =
  rev [] ys ≡⟨ rev-[] ys ⟩
  ys        ≡⟨ sym $ ++-leftIdentity Fys ⟩
  [] ++ ys  ≡⟨ subst (λ t → [] ++ ys ≡ t ++ ys)
                     (sym $ rev-[] [])
                     refl
            ⟩
  rev [] [] ++ ys ∎
rev-++-commute {ys = ys} (consF {x} {xs} Tx Fxs) Fys =
  rev (x ∷ xs) ys
    ≡⟨ rev-∷ x xs ys ⟩
  rev xs (x ∷ ys)
    ≡⟨ rev-++-commute Fxs (consF Tx Fys) ⟩  -- IH.
  rev xs [] ++ x ∷ ys
    ≡⟨ subst (λ t → rev xs [] ++ x ∷ ys ≡ rev xs [] ++ t)
             (sym
               ( (x ∷ []) ++ ys
                    ≡⟨ ++-∷ x [] ys ⟩
                 x ∷ ([] ++ ys)
                   ≡⟨ subst (λ t → x ∷ ([] ++ ys) ≡ x ∷ t)
                            (++-leftIdentity Fys)
                            refl
                   ⟩
                 x ∷ ys ∎
               )
             )
             refl
    ⟩
  rev xs [] ++ (x ∷ []) ++ ys
    ≡⟨ sym $ ++-assoc (rev-Forest Fxs nilF) (consF Tx nilF) Fys ⟩
  (rev xs [] ++ (x ∷ [])) ++ ys
    ≡⟨ subst (λ t → (rev xs [] ++ (x ∷ [])) ++ ys ≡ t ++ ys)
             (sym $ rev-++-commute Fxs (consF Tx nilF))  -- IH.
             refl
    ⟩
  rev xs (x ∷ []) ++ ys
    ≡⟨ subst (λ t → rev xs (x ∷ []) ++ ys ≡ t ++ ys)
             (sym $ rev-∷ x xs [])
             refl
    ⟩
  rev (x ∷ xs) [] ++ ys ∎

reverse-++-commute : ∀ {xs ys} → Forest xs → Forest ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} nilF Fys =
  reverse ([] ++ ys)
    ≡⟨ subst (λ t → reverse ([] ++ ys) ≡ reverse t) (++-[] ys) refl ⟩
  reverse ys
    ≡⟨ sym (++-rightIdentity (reverse-Forest Fys)) ⟩
  reverse ys ++ []
    ≡⟨ subst (λ t → reverse ys ++ [] ≡ reverse ys ++ t) (sym (rev-[] [])) refl ⟩
  reverse ys ++ reverse [] ∎

reverse-++-commute (consF {x} {xs} Tx Fxs) nilF =
  reverse ((x ∷ xs) ++ [])
    ≡⟨ subst (λ t → reverse ((x ∷ xs) ++ []) ≡ reverse t)
             (++-rightIdentity (consF Tx Fxs))
             refl
    ⟩
  reverse (x ∷ xs)
    ≡⟨ sym (++-[] (reverse (x ∷ xs))) ⟩
  [] ++ reverse (x ∷ xs)
     ≡⟨ subst (λ t → [] ++ reverse (x ∷ xs) ≡ t ++ reverse (x ∷ xs))
              (sym (rev-[] []))
              refl
     ⟩
  reverse [] ++ reverse (x ∷ xs) ∎

reverse-++-commute (consF {x} {xs} Tx Fxs) (consF {y} {ys} Ty Fys) =
  reverse ((x ∷ xs) ++ y ∷ ys)
    ≡⟨ refl ⟩
  rev ((x ∷ xs) ++ y ∷ ys) []
    ≡⟨ subst (λ t → rev ((x ∷ xs) ++ y ∷ ys) [] ≡ rev t [])
             (++-∷ x xs (y ∷ ys))
             refl
    ⟩
  rev (x ∷ (xs ++ y ∷ ys)) []
    ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
  rev (xs ++ y ∷ ys) (x ∷ [])
    ≡⟨ rev-++-commute (++-Forest Fxs (consF Ty Fys)) (consF Tx nilF) ⟩
  rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
    ≡⟨ subst (λ t → rev (xs ++ y ∷ ys) [] ++ (x ∷ []) ≡ t ++ (x ∷ []))
             refl
             refl
    ⟩
  reverse (xs ++ y ∷ ys) ++ (x ∷ [])
    ≡⟨ subst (λ t → reverse (xs ++ y ∷ ys) ++ (x ∷ []) ≡ t ++ (x ∷ []))
             (reverse-++-commute Fxs (consF Ty Fys))  -- IH.
             refl
    ⟩
  (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
    ≡⟨ ++-assoc (reverse-Forest (consF Ty Fys))
                (reverse-Forest Fxs)
                (consF Tx nilF)
    ⟩
  reverse (y ∷ ys) ++ reverse xs ++ x ∷ []
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ reverse xs ++ x ∷ [] ≡
                    reverse (y ∷ ys) ++ t ++ x ∷ [])
             refl
             refl
    ⟩
  reverse (y ∷ ys) ++ rev xs [] ++ x ∷ []
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ rev xs [] ++ x ∷ [] ≡
                    reverse (y ∷ ys) ++ t)
             (sym $ rev-++-commute Fxs (consF Tx nilF))
             refl
    ⟩
  reverse (y ∷ ys) ++ rev xs (x ∷ [])
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ rev xs (x ∷ []) ≡
                    reverse (y ∷ ys) ++ t)
             (sym $ rev-∷ x xs [])
             refl
    ⟩
  reverse (y ∷ ys) ++ rev (x ∷ xs) []
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ rev (x ∷ xs) [] ≡
                    reverse (y ∷ ys) ++ t)
             refl
             refl
    ⟩
  reverse (y ∷ ys) ++ reverse (x ∷ xs) ∎

reverse-∷ : ∀ {x ys} → Tree x → Forest ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ {x} Tx nilF =
  rev (x ∷ []) []
    ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ [])
    ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []
    ≡⟨ sym (++-leftIdentity (consF Tx nilF)) ⟩
  [] ++ x ∷ []
     ≡⟨ subst (λ p → [] ++ x ∷ [] ≡ p ++ x ∷ []) (sym (rev-[] [])) refl ⟩
  rev [] [] ++ x ∷ [] ∎

reverse-∷ {x} Tx (consF {y} {ys} Ty Fys) = sym
  ( reverse (y ∷ ys) ++ x ∷ []
      ≡⟨ subst (λ p → reverse (y ∷ ys) ++ x ∷ [] ≡ reverse (y ∷ ys) ++ p)
               (sym (reverse-[x]≡[x] x))
               refl
      ⟩
    (reverse (y ∷ ys) ++ reverse (x ∷ []))
      ≡⟨ sym (reverse-++-commute (consF Tx nilF) (consF Ty Fys)) ⟩
    reverse ((x ∷ []) ++ (y ∷ ys))
      ≡⟨ subst (λ p → reverse ((x ∷ []) ++ (y ∷ ys)) ≡ reverse p)
               (++-∷ x [] (y ∷ ys))
               refl
      ⟩
    reverse (x ∷ ([] ++ (y ∷ ys)))
      ≡⟨ subst (λ p → reverse (x ∷ ([] ++ (y ∷ ys))) ≡ reverse (x ∷ p))
               (++-leftIdentity (consF Ty Fys))
               refl
      ⟩
    reverse (x ∷ y ∷ ys) ∎
  )

map-++-commute : ∀ f {xs ys} → (∀ {x} → Tree x → Tree (f · x)) →
                 Forest xs → Forest ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f {ys = ys} fTree nilF Fys =
  map f ([] ++ ys)
    ≡⟨ subst (λ t → map f ([] ++ ys) ≡ map f t) (++-[] ys) refl ⟩
  map f ys
    ≡⟨ sym (++-leftIdentity (map-Forest f fTree Fys)) ⟩
  [] ++ map f ys
     ≡⟨ subst (λ t → [] ++ map f ys ≡ t ++ map f ys) (sym (map-[] f)) refl ⟩
  map f [] ++ map f ys ∎

map-++-commute f {ys = ys} fTree (consF {x} {xs} Tx Fxs) Fys =
  map f ((x ∷ xs) ++ ys)
    ≡⟨ subst (λ t → map f ((x ∷ xs) ++ ys) ≡ map f t) (++-∷ x xs ys) refl ⟩
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
  map f (x ∷ xs) ++ map f ys ∎
