------------------------------------------------------------------------------
-- Properties related with lists of trees
------------------------------------------------------------------------------

module Draft.Mirror.ListTree.PropertiesI where

open import LTC.Base

open import Common.Function

open import Draft.Mirror.Mirror

open import LTC.Data.List

open import LTC.Relation.Binary.EqReasoning

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

++-leftIdentity : ∀ {xs} → ListTree xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → ListTree xs → xs ++ [] ≡ xs
++-rightIdentity nilLT               = ++-[] []
++-rightIdentity (consLT {x} {xs} Tx LTxs) =
  begin
    (x ∷ xs) ++ []
      ≡⟨ ++-∷ x xs [] ⟩
    x ∷ (xs ++ [])
      ≡⟨ subst (λ t → x ∷ (xs ++ []) ≡ x ∷ t)
               (++-rightIdentity LTxs) -- IH.
               refl
      ⟩
    x ∷ xs
  ∎

++-assoc : ∀ {xs ys zs} → ListTree xs → ListTree ys → ListTree zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {ys = ys} {zs} nilLT LTys LTzs =
  begin
    ([] ++ ys) ++ zs
      ≡⟨ subst (λ t → ([] ++ ys) ++ zs ≡ t ++ zs)
               (++-[] ys)
               refl
      ⟩
    ys ++ zs
      ≡⟨ sym (++-leftIdentity (++-ListTree LTys LTzs)) ⟩
    [] ++ ys ++ zs
  ∎

++-assoc {ys = ys} {zs} (consLT {x} {xs} Tx LTxs) LTys LTzs =
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
               (++-assoc LTxs LTys LTzs) -- IH.
               refl
      ⟩
    x ∷ (xs ++ ys ++ zs)
      ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
    (x ∷ xs) ++ ys ++ zs
  ∎

rev-++-commute : ∀ {xs ys} → ListTree xs → ListTree ys →
                 rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilLT LTys =
  begin
    rev [] ys ≡⟨ rev-[] ys ⟩
    ys        ≡⟨ sym $ ++-leftIdentity LTys ⟩
    [] ++ ys  ≡⟨ subst (λ t → [] ++ ys ≡ t ++ ys)
                       (sym $ rev-[] [])
                       refl
              ⟩
    rev [] [] ++ ys
  ∎
rev-++-commute {ys = ys} (consLT {x} {xs} Tx LTxs) LTys =
  begin
    rev (x ∷ xs) ys      ≡⟨ rev-∷ x xs ys ⟩
    rev xs (x ∷ ys)      ≡⟨ rev-++-commute LTxs (consLT Tx LTys) ⟩  -- IH.
    rev xs [] ++ x ∷ ys
      ≡⟨ subst (λ t → rev xs [] ++ x ∷ ys ≡ rev xs [] ++ t)
               (sym
                 ( begin
                     (x ∷ []) ++ ys ≡⟨ ++-∷ x [] ys ⟩
                     x ∷ ([] ++ ys) ≡⟨ subst (λ t → x ∷ ([] ++ ys) ≡ x ∷ t)
                                             (++-leftIdentity LTys)
                                             refl
                                    ⟩
                     x ∷ ys
                   ∎
                 )
               )
               refl
      ⟩
    rev xs [] ++ (x ∷ []) ++ ys
      ≡⟨ sym $ ++-assoc (rev-ListTree LTxs nilLT) (consLT Tx nilLT) LTys ⟩
    (rev xs [] ++ (x ∷ [])) ++ ys
      ≡⟨ subst (λ t → (rev xs [] ++ (x ∷ [])) ++ ys ≡ t ++ ys)
               (sym $ rev-++-commute LTxs (consLT Tx nilLT))  -- IH.
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
  -- TODO: See the ATP proof.
  reverse-∷ : ∀ x {ys} → ListTree ys →
              reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])

reverse-++ : ∀ {xs ys} → ListTree xs → ListTree ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} nilLT LTys =
  begin
    reverse ([] ++ ys)
      ≡⟨ subst (λ t → reverse ([] ++ ys) ≡ reverse t)
               (++-[] ys)
               refl
      ⟩
    reverse ys
      ≡⟨ sym (++-rightIdentity (rev-ListTree LTys nilLT)) ⟩
    reverse ys ++ []
      ≡⟨ subst (λ t → reverse ys ++ [] ≡ reverse ys ++ t)
               (sym (rev-[] []))
               refl
      ⟩
    reverse ys ++ reverse []
  ∎

reverse-++ (consLT {x} {xs} Tx LTxs) nilLT =
  begin
    reverse ((x ∷ xs) ++ [])
      ≡⟨ subst (λ t → reverse ((x ∷ xs) ++ []) ≡ reverse t)
               (++-rightIdentity (consLT Tx LTxs))
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

reverse-++ (consLT {x} {xs} Tx LTxs) (consLT {y} {ys} Ty LTys) =
  begin
    reverse ((x ∷ xs) ++ y ∷ ys) ≡⟨ refl ⟩
    rev ((x ∷ xs) ++ y ∷ ys) []
      ≡⟨ subst (λ t → rev ((x ∷ xs) ++ y ∷ ys) [] ≡ rev t [])
               (++-∷ x xs (y ∷ ys))
               refl
      ⟩
    rev (x ∷ (xs ++ y ∷ ys)) [] ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
    rev (xs ++ y ∷ ys) (x ∷ [])
      ≡⟨ rev-++-commute (++-ListTree LTxs (consLT Ty LTys)) (consLT Tx nilLT) ⟩
    rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
      ≡⟨ subst (λ t → rev (xs ++ y ∷ ys) [] ++ (x ∷ []) ≡ t ++ (x ∷ []))
               refl
               refl
      ⟩
    reverse (xs ++ y ∷ ys) ++ (x ∷ [])
      ≡⟨ subst (λ t → reverse (xs ++ y ∷ ys) ++ (x ∷ []) ≡ t ++ (x ∷ []))
               (reverse-++ LTxs (consLT Ty LTys))  -- IH.
               refl
      ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ ++-assoc (rev-ListTree (consLT Ty LTys) nilLT)
                  (rev-ListTree LTxs nilLT)
                  (consLT Tx nilLT)
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
               (sym $ rev-++-commute LTxs (consLT Tx nilLT))
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
