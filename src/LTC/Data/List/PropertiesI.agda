------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.PropertiesI where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.List
open import LTC.Data.List.Type

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Closure properties

-- See the ATP proof.
postulate
  ++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)

-- See the ATP proof.
postulate
  rev-List : ∀ {xs ys} → List xs → List ys → List (rev xs ys)

++-leftIdentity : ∀ {xs} → List xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

-- See the ATP proof.
postulate
  ++-assoc : ∀ {xs ys zs} → List xs → List ys → List zs →
             (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

rev-++ : ∀ {xs ys} → List xs → List ys → rev xs ys ≡ rev xs [] ++ ys
rev-++ {ys = ys} nilL Lys =
  begin
    rev [] ys ≡⟨ rev-[] ys ⟩
    ys        ≡⟨ sym $ ++-leftIdentity Lys ⟩
    [] ++ ys  ≡⟨ subst (λ t → [] ++ ys ≡ t ++ ys)
                       (sym $ rev-[] [])
                       refl
              ⟩
    rev [] [] ++ ys
  ∎
rev-++ {ys = ys} (consL x {xs} Lxs) Lys =
  begin
    rev (x ∷ xs) ys      ≡⟨ rev-∷ x xs ys ⟩
    rev xs (x ∷ ys)      ≡⟨ rev-++ Lxs (consL x Lys) ⟩  -- IH.
    rev xs [] ++ x ∷ ys
      ≡⟨ subst (λ t → rev xs [] ++ x ∷ ys ≡ rev xs [] ++ t)
               (sym
                 ( begin
                     (x ∷ []) ++ ys ≡⟨ ++-∷ x [] ys ⟩
                     x ∷ ([] ++ ys) ≡⟨ subst (λ t → x ∷ ([] ++ ys) ≡ x ∷ t)
                                             (++-leftIdentity Lys)
                                             refl
                                    ⟩
                     x ∷ ys
                   ∎
                 )
               )
               refl
      ⟩
    rev xs [] ++ (x ∷ []) ++ ys
      ≡⟨ sym $ ++-assoc (rev-List Lxs nilL) (consL x nilL) Lys ⟩
    (rev xs [] ++ (x ∷ [])) ++ ys
      ≡⟨ subst (λ t → (rev xs [] ++ (x ∷ [])) ++ ys ≡ t ++ ys)
               (sym $ rev-++ Lxs (consL x nilL))  -- IH.
               refl
      ⟩
    rev xs (x ∷ []) ++ ys
      ≡⟨ subst (λ t → rev xs (x ∷ []) ++ ys ≡ t ++ ys)
               (sym $ rev-∷ x xs [])
               refl
      ⟩
    rev (x ∷ xs) [] ++ ys
  ∎

reverse-++ : ∀ {xs ys} → List xs → List ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} nilL Lys = prf
  where
    -- See the ATP proof.
    postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []

reverse-++ (consL x {xs} Lxs) nilL = prf
  where
    -- See the ATP proof.
    postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
reverse-++ (consL x {xs} Lxs) (consL y {ys} Lys) =
  begin
    reverse ((x ∷ xs) ++ y ∷ ys) ≡⟨ refl ⟩
    rev ((x ∷ xs) ++ y ∷ ys) []
      ≡⟨ subst (λ t → rev ((x ∷ xs) ++ y ∷ ys) [] ≡ rev t [])
               (++-∷ x xs (y ∷ ys))
               refl
      ⟩
    rev (x ∷ (xs ++ y ∷ ys)) [] ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
    rev (xs ++ y ∷ ys) (x ∷ [])
      ≡⟨ rev-++ (++-List Lxs (consL y Lys)) (consL x nilL) ⟩
    rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
      ≡⟨ subst (λ t → rev (xs ++ y ∷ ys) [] ++ (x ∷ []) ≡ t ++ (x ∷ []))
               refl
               refl
      ⟩
    reverse (xs ++ y ∷ ys) ++ (x ∷ [])
      ≡⟨ subst (λ t → reverse (xs ++ y ∷ ys) ++ (x ∷ []) ≡ t ++ (x ∷ []))
               (reverse-++ Lxs (consL y Lys))  -- IH.
               refl
      ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ ++-assoc (rev-List (consL y Lys) nilL)
                  (rev-List Lxs nilL)
                  (consL x nilL)
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
               (sym $ rev-++ Lxs (consL x nilL))
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
    reverse (y ∷ ys) ++ reverse (x ∷ xs)
  ∎
