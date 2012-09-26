------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.Conat
open import FOTC.Data.List
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Totality properties

length-N : ∀ {xs} → List xs → N (length xs)
length-N lnil               = subst N (sym length-[]) nzero
length-N (lcons x {xs} Lxs) = subst N (sym (length-∷ x xs)) (nsucc (length-N Lxs))

++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)
++-List {ys = ys} lnil               Lys = subst List (sym (++-[] ys)) Lys
++-List {ys = ys} (lcons x {xs} Lxs) Lys =
  subst List (sym (++-∷ x xs ys)) (lcons x (++-List Lxs Lys))

map-List : ∀ f {xs} → List xs → List (map f xs)
map-List f lnil               = subst List (sym (map-[] f)) lnil
map-List f (lcons x {xs} Lxs) =
  subst List (sym (map-∷ f x xs)) (lcons (f · x) (map-List f Lxs))

rev-List : ∀ {xs ys} → List xs → List ys → List (rev xs ys)
rev-List {ys = ys} lnil               Lys = subst List (sym (rev-[] ys)) Lys
rev-List {ys = ys} (lcons x {xs} Lxs) Lys =
  subst List (sym (rev-∷ x xs ys)) (rev-List Lxs (lcons x Lys))

reverse-List : ∀ {xs} → List xs → List (reverse xs)
reverse-List Lxs = rev-List Lxs lnil

-- Length properties

lg-x<lg-x∷xs : ∀ x {xs} → List xs → LT (length xs) (length (x ∷ xs))
lg-x<lg-x∷xs x lnil =
  length [] < length (x ∷ [])
    ≡⟨ subst₂ (λ t₁ t₂ → length [] < length (x ∷ []) ≡ t₁ < t₂)
              length-[]
              (length-∷ x [])
              refl
    ⟩
  zero < succ₁ (length [])
    ≡⟨ <-0S (length []) ⟩
  true ∎

lg-x<lg-x∷xs x (lcons y {xs} Lxs) =
  length (y ∷ xs) < length (x ∷ y ∷ xs)
    ≡⟨ subst₂ (λ t₁ t₂ → length (y ∷ xs) < length (x ∷ y ∷ xs) ≡ t₁ < t₂)
              (length-∷ y xs)
              (length-∷ x (y ∷ xs))
              refl
    ⟩
  succ₁ (length xs) < succ₁ (length (y ∷ xs))
    ≡⟨ <-SS (length xs) (length (y ∷ xs)) ⟩
  length xs < length (y ∷ xs)
    ≡⟨ lg-x<lg-x∷xs y Lxs ⟩
  true ∎

lg-xs<lg-[]→⊥ : ∀ {xs} → List xs → ¬ (LT (length xs) (length []))
lg-xs<lg-[]→⊥ lnil lg-[]<lg-[] = ⊥-elim (0<0→⊥ helper)
  where
  helper : zero < zero ≡ true
  helper =
    zero < zero
      ≡⟨ subst₂ (λ t₁ t₂ → zero < zero ≡ t₁ < t₂)
                (sym length-[])
                (sym length-[])
                refl
      ⟩
    length [] < length []
      ≡⟨ lg-[]<lg-[] ⟩
    true ∎

lg-xs<lg-[]→⊥ (lcons x {xs} Lxs) lg-x∷xs<lg-[] = ⊥-elim (S<0→⊥ helper)
  where
  helper : succ₁ (length xs) < zero ≡ true
  helper =
    succ₁ (length xs) < zero
      ≡⟨ subst₂ (λ t₁ t₂ → succ₁ (length xs) < zero ≡ t₁ < t₂)
                (sym (length-∷ x xs))
                (sym length-[])
                refl
      ⟩
    length (x ∷ xs) < length []
      ≡⟨ lg-x∷xs<lg-[] ⟩
    true ∎

lg-xs≡∞→lg-x∷xs≡∞ : ∀ x xs → length xs ≡ ∞ → length (x ∷ xs) ≡ ∞
lg-xs≡∞→lg-x∷xs≡∞ x xs h =
  length (x ∷ xs) ≡⟨ length-∷ x xs ⟩
  succ₁ (length xs) ≡⟨ succCong h ⟩
  succ₁ ∞ ≡⟨ sym ∞-eq ⟩
  ∞ ∎

-- Append properties

++-leftIdentity : ∀ xs → [] ++ xs ≡ xs
++-leftIdentity = ++-[]

++-rightIdentity : ∀ {xs} → List xs → xs ++ [] ≡ xs
++-rightIdentity lnil               = ++-[] []
++-rightIdentity (lcons x {xs} Lxs) =
  (x ∷ xs) ++ []
     ≡⟨ ++-∷ x xs [] ⟩
  x ∷ (xs ++ [])
    ≡⟨ subst (λ t → x ∷ (xs ++ []) ≡ x ∷ t) (++-rightIdentity Lxs) refl ⟩
  x ∷ xs ∎

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc lnil ys zs =
  ([] ++ ys) ++ zs
    ≡⟨ subst (λ t → ([] ++ ys) ++ zs ≡ t ++ zs) (++-[] ys) refl ⟩
  ys ++ zs
     ≡⟨ sym (++-leftIdentity (ys ++ zs)) ⟩
  [] ++ ys ++ zs ∎

++-assoc (lcons x {xs} Lxs) ys zs =
  ((x ∷ xs) ++ ys) ++ zs
    ≡⟨ subst (λ t → ((x ∷ xs) ++ ys) ++ zs ≡ t ++ zs) (++-∷ x xs ys) refl ⟩
  (x ∷ (xs ++ ys)) ++ zs
     ≡⟨ ++-∷ x (xs ++ ys) zs ⟩
  x ∷ ((xs ++ ys) ++ zs)
    ≡⟨ subst (λ t → x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ t)
             (++-assoc Lxs ys zs)
             refl
    ⟩
  x ∷ (xs ++ ys ++ zs)
    ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
  (x ∷ xs) ++ ys ++ zs ∎

-- Map properties

map-++-commute : ∀ f {xs} → List xs → ∀ ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f lnil ys =
  map f ([] ++ ys)
    ≡⟨ subst (λ t → map f ([] ++ ys) ≡ map f t) (++-[] ys) refl ⟩
  map f ys
    ≡⟨ sym (++-leftIdentity (map f ys)) ⟩
  [] ++ map f ys
     ≡⟨ subst (λ t → [] ++ map f ys ≡ t ++ map f ys) (sym (map-[] f)) refl
     ⟩
  map f [] ++ map f ys ∎

map-++-commute f (lcons x {xs} Lxs) ys =
  map f ((x ∷ xs) ++ ys)
    ≡⟨ subst (λ t → map f ((x ∷ xs) ++ ys) ≡ map f t) (++-∷ x xs ys) refl ⟩
  map f (x ∷ xs ++ ys)
    ≡⟨ map-∷ f x (xs ++ ys) ⟩
  f · x ∷ map f (xs ++ ys)
    ≡⟨ subst (λ t → f · x ∷ map f (xs ++ ys) ≡ f · x ∷ t)
             (map-++-commute f Lxs ys)
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

map≡[] : ∀ {f xs} → List xs → map f xs ≡ [] → xs ≡ []
map≡[] lnil                   h = refl
map≡[] {f} (lcons x {xs} Lxs) h = ⊥-elim ([]≢cons (trans (sym h) (map-∷ f x xs)))

-- Reverse properties

reverse-[x]≡[x] : ∀ x → reverse (x ∷ []) ≡ x ∷ []
reverse-[x]≡[x] x =
  rev (x ∷ []) [] ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ []) ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []          ∎

rev-++-commute : ∀ {xs} → List xs → ∀ ys → rev xs ys ≡ rev xs [] ++ ys
rev-++-commute lnil ys =
  rev [] ys       ≡⟨ rev-[] ys ⟩
  ys              ≡⟨ sym $ ++-leftIdentity ys ⟩
  [] ++ ys        ≡⟨ subst (λ t → [] ++ ys ≡ t ++ ys) (sym $ rev-[] []) refl ⟩
  rev [] [] ++ ys ∎

rev-++-commute (lcons x {xs} Lxs) ys =
  rev (x ∷ xs) ys
    ≡⟨ rev-∷ x xs ys ⟩
  rev xs (x ∷ ys)
    ≡⟨ rev-++-commute Lxs (x ∷ ys) ⟩
  rev xs [] ++ x ∷ ys
    ≡⟨ subst (λ t → rev xs [] ++ x ∷ ys ≡ rev xs [] ++ t)
             (sym
               ( (x ∷ []) ++ ys
                    ≡⟨ ++-∷ x [] ys ⟩
                 x ∷ ([] ++ ys)
                   ≡⟨ subst (λ t → x ∷ ([] ++ ys) ≡ x ∷ t)
                            (++-leftIdentity ys)
                            refl
                   ⟩
                 x ∷ ys ∎
               )
             )
             refl
    ⟩
  rev xs [] ++ (x ∷ []) ++ ys
    ≡⟨ sym $ ++-assoc (rev-List Lxs lnil) (x ∷ []) ys ⟩
  (rev xs [] ++ (x ∷ [])) ++ ys
    ≡⟨ subst (λ t → (rev xs [] ++ (x ∷ [])) ++ ys ≡ t ++ ys)
             (sym $ rev-++-commute Lxs (x ∷ []))
             refl
    ⟩
  rev xs (x ∷ []) ++ ys
    ≡⟨ subst (λ t → rev xs (x ∷ []) ++ ys ≡ t ++ ys)
             (sym $ rev-∷ x xs [])
             refl
    ⟩
  rev (x ∷ xs) [] ++ ys ∎

reverse-++-commute : ∀ {xs ys} → List xs → List ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} lnil Lys =
  reverse ([] ++ ys)
    ≡⟨ subst (λ t → reverse ([] ++ ys) ≡ reverse t) (++-[] ys) refl ⟩
  reverse ys
    ≡⟨ sym (++-rightIdentity (reverse-List Lys)) ⟩
  reverse ys ++ []
    ≡⟨ subst (λ t → reverse ys ++ [] ≡ reverse ys ++ t) (sym (rev-[] [])) refl ⟩
    reverse ys ++ reverse [] ∎

reverse-++-commute (lcons x {xs} Lxs) lnil =
  reverse ((x ∷ xs) ++ [])
    ≡⟨ subst (λ t → reverse ((x ∷ xs) ++ []) ≡ reverse t)
             (++-rightIdentity (lcons x Lxs))
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

reverse-++-commute (lcons x {xs} Lxs) (lcons y {ys} Lys) =
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
    ≡⟨ rev-++-commute (++-List Lxs (lcons y Lys)) (x ∷ []) ⟩
  rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
    ≡⟨ subst (λ t → rev (xs ++ y ∷ ys) [] ++ (x ∷ []) ≡ t ++ (x ∷ []))
             refl
             refl
    ⟩
  reverse (xs ++ y ∷ ys) ++ (x ∷ [])
    ≡⟨ subst (λ t → reverse (xs ++ y ∷ ys) ++ (x ∷ []) ≡ t ++ (x ∷ []))
             (reverse-++-commute Lxs (lcons y Lys))
             refl
    ⟩
  (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
    ≡⟨ ++-assoc (reverse-List (lcons y Lys)) (reverse xs) (x ∷ []) ⟩
  reverse (y ∷ ys) ++ reverse xs ++ x ∷ []
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ reverse xs ++ x ∷ [] ≡
                    reverse (y ∷ ys) ++ t ++ x ∷ [])
             refl
             refl
    ⟩
  reverse (y ∷ ys) ++ rev xs [] ++ x ∷ []
    ≡⟨ subst (λ t → reverse (y ∷ ys) ++ rev xs [] ++ x ∷ [] ≡
                    reverse (y ∷ ys) ++ t)
             (sym $ rev-++-commute Lxs (x ∷ []))
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

reverse-∷ : ∀ x {ys} → List ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ x lnil =
  rev (x ∷ []) []
    ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ [])
    ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []
    ≡⟨ sym (++-leftIdentity (x ∷ [])) ⟩
  [] ++ x ∷ []
    ≡⟨ subst (λ p → [] ++ x ∷ [] ≡ p ++ x ∷ []) (sym (rev-[] [])) refl ⟩
  rev [] [] ++ x ∷ [] ∎

reverse-∷ x (lcons y {ys} Lys) = sym
  ( reverse (y ∷ ys) ++ x ∷ []
      ≡⟨ subst (λ p → reverse (y ∷ ys) ++ x ∷ [] ≡ reverse (y ∷ ys) ++ p)
               (sym (reverse-[x]≡[x] x))
               refl
      ⟩
    (reverse (y ∷ ys) ++ reverse (x ∷ []))
      ≡⟨ sym (reverse-++-commute (lcons x lnil) (lcons y Lys)) ⟩
    reverse ((x ∷ []) ++ (y ∷ ys))
      ≡⟨ subst (λ p → reverse ((x ∷ []) ++ (y ∷ ys)) ≡ reverse p)
               (++-∷ x [] (y ∷ ys))
               refl
      ⟩
    reverse (x ∷ ([] ++ (y ∷ ys)))
      ≡⟨ subst (λ p → reverse (x ∷ ([] ++ (y ∷ ys))) ≡ reverse (x ∷ p))
               (++-leftIdentity (y ∷ ys))
               refl
      ⟩
    reverse (x ∷ y ∷ ys) ∎
  )
