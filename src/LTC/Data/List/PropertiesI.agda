------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.PropertiesI where

open import LTC.Base

open import Common.Function

open import LTC.Data.List
open import LTC.Data.List.Type

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)
++-List {ys = ys} nilL               Lys = subst List (sym (++-[] ys)) Lys
++-List {ys = ys} (consL x {xs} Lxs) Lys =
  subst List (sym (++-∷ x xs ys)) (consL x (++-List Lxs Lys))

map-List : ∀ {xs} f → List xs → List (map f xs)
map-List f nilL = subst List (sym (map-[] f)) nilL
map-List f (consL x {xs} Lxs) =
  subst List (sym (map-∷ f x xs)) (consL (f · x) (map-List f Lxs))

rev-List : ∀ {xs ys} → List xs → List ys → List (rev xs ys)
rev-List {ys = ys} nilL          Lys = subst List (sym (rev-[] ys)) Lys
rev-List {ys = ys} (consL x {xs} Lxs) Lys =
  subst List (sym (rev-∷ x xs ys)) (rev-List Lxs (consL x Lys))

reverse-List : ∀ {xs} → List xs → List (reverse xs)
reverse-List Lxs = rev-List Lxs nilL

++-leftIdentity : ∀ {xs} → List xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → List xs → xs ++ [] ≡ xs
++-rightIdentity nilL               = ++-[] []
++-rightIdentity (consL x {xs} Lxs) =
  begin
    (x ∷ xs) ++ []
      ≡⟨ ++-∷ x xs [] ⟩
    x ∷ (xs ++ [])
      ≡⟨ subst (λ t → x ∷ (xs ++ []) ≡ x ∷ t)
               (++-rightIdentity Lxs)
               refl
      ⟩
    x ∷ xs
  ∎

++-assoc : ∀ {xs ys zs} → List xs → List ys → List zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {ys = ys} {zs} nilL Lys Lzs =
  begin
    ([] ++ ys) ++ zs
      ≡⟨ subst (λ t → ([] ++ ys) ++ zs ≡ t ++ zs)
               (++-[] ys)
               refl
      ⟩
    ys ++ zs
      ≡⟨ sym (++-leftIdentity (++-List Lys Lzs)) ⟩
    [] ++ ys ++ zs
  ∎

++-assoc {ys = ys} {zs} (consL x {xs} Lxs) Lys Lzs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
      ≡⟨ subst (λ t → ((x ∷ xs) ++ ys) ++ zs ≡ t ++ zs)
               (++-∷ x xs ys)
               refl
      ⟩
    (x ∷ (xs ++ ys)) ++ zs
      ≡⟨ ++-∷ x (xs ++ ys) zs ⟩
    x ∷ ((xs ++ ys) ++ zs)
      ≡⟨ subst (λ t → x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ t)
               (++-assoc Lxs Lys Lzs) -- IH.
               refl
      ⟩
    x ∷ (xs ++ ys ++ zs)
      ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
    (x ∷ xs) ++ ys ++ zs
  ∎

-- N.B. This property does not depend of the type of lists.
reverse-[x]≡[x] : ∀ x → reverse (x ∷ []) ≡ x ∷ []
reverse-[x]≡[x] x =
  begin
    rev (x ∷ []) []
      ≡⟨ rev-∷ x [] [] ⟩
    rev [] (x ∷ [])
      ≡⟨ rev-[] (x ∷ []) ⟩
    x ∷ []
  ∎

rev-++-commute : ∀ {xs ys} → List xs → List ys → rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilL Lys =
  begin
    rev [] ys ≡⟨ rev-[] ys ⟩
    ys        ≡⟨ sym $ ++-leftIdentity Lys ⟩
    [] ++ ys  ≡⟨ subst (λ t → [] ++ ys ≡ t ++ ys)
                       (sym $ rev-[] [])
                       refl
              ⟩
    rev [] [] ++ ys
  ∎
rev-++-commute {ys = ys} (consL x {xs} Lxs) Lys =
  begin
    rev (x ∷ xs) ys      ≡⟨ rev-∷ x xs ys ⟩
    rev xs (x ∷ ys)      ≡⟨ rev-++-commute Lxs (consL x Lys) ⟩  -- IH.
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
               (sym $ rev-++-commute Lxs (consL x nilL))  -- IH.
               refl
      ⟩
    rev xs (x ∷ []) ++ ys
      ≡⟨ subst (λ t → rev xs (x ∷ []) ++ ys ≡ t ++ ys)
               (sym $ rev-∷ x xs [])
               refl
      ⟩
    rev (x ∷ xs) [] ++ ys
  ∎

postulate
  -- See the ATP proof.
  reverse-∷ : ∀ x {ys} → List ys → reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])

reverse-++-commute : ∀ {xs ys} → List xs → List ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} nilL Lys =
  begin
    reverse ([] ++ ys)
      ≡⟨ subst (λ t → reverse ([] ++ ys) ≡ reverse t)
               (++-[] ys)
               refl
      ⟩
    reverse ys
      ≡⟨ sym (++-rightIdentity (reverse-List Lys)) ⟩
    reverse ys ++ []
      ≡⟨ subst (λ t → reverse ys ++ [] ≡ reverse ys ++ t)
               (sym (rev-[] []))
               refl
      ⟩
    reverse ys ++ reverse []
  ∎

reverse-++-commute (consL x {xs} Lxs) nilL =
  begin
    reverse ((x ∷ xs) ++ [])
      ≡⟨ subst (λ t → reverse ((x ∷ xs) ++ []) ≡ reverse t)
               (++-rightIdentity (consL x Lxs))
               refl
      ⟩
    reverse (x ∷ xs)
      ≡⟨ sym (++-[] (reverse (x ∷ xs))) ⟩
    [] ++ reverse (x ∷ xs)
      ≡⟨ subst (λ t → [] ++ reverse (x ∷ xs) ≡ t ++ reverse (x ∷ xs))
               (sym (rev-[] []))
               refl
      ⟩
    reverse [] ++ reverse (x ∷ xs)
  ∎

reverse-++-commute (consL x {xs} Lxs) (consL y {ys} Lys) =
  begin
    reverse ((x ∷ xs) ++ y ∷ ys) ≡⟨ refl ⟩
    rev ((x ∷ xs) ++ y ∷ ys) []
      ≡⟨ subst (λ t → rev ((x ∷ xs) ++ y ∷ ys) [] ≡ rev t [])
               (++-∷ x xs (y ∷ ys))
               refl
      ⟩
    rev (x ∷ (xs ++ y ∷ ys)) [] ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
    rev (xs ++ y ∷ ys) (x ∷ [])
      ≡⟨ rev-++-commute (++-List Lxs (consL y Lys)) (consL x nilL) ⟩
    rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
      ≡⟨ subst (λ t → rev (xs ++ y ∷ ys) [] ++ (x ∷ []) ≡ t ++ (x ∷ []))
               refl
               refl
      ⟩
    reverse (xs ++ y ∷ ys) ++ (x ∷ [])
      ≡⟨ subst (λ t → reverse (xs ++ y ∷ ys) ++ (x ∷ []) ≡ t ++ (x ∷ []))
               (reverse-++-commute Lxs (consL y Lys))  -- IH.
               refl
      ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ ++-assoc (reverse-List (consL y Lys))
                  (reverse-List Lxs)
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
               (sym $ rev-++-commute Lxs (consL x nilL))
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

map-++-commute : ∀ f {xs ys} → List xs → List ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f {ys = ys} nilL Lys =
  begin
    map f ([] ++ ys)
      ≡⟨ subst (λ t → map f ([] ++ ys) ≡ map f t)
               (++-[] ys)
               refl
      ⟩
    map f ys
      ≡⟨ sym (++-leftIdentity (map-List f Lys)) ⟩
    [] ++ map f ys
      ≡⟨ subst (λ t → [] ++ map f ys ≡ t ++ map f ys)
               (sym (map-[] f))
               refl
      ⟩
    map f [] ++ map f ys
  ∎

map-++-commute f {ys = ys} (consL x {xs} Lxs) Lys =
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
               (map-++-commute f Lxs Lys)  -- IH.
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
