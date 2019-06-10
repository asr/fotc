------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.List.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Base.Properties
open import Interactive.FOTC.Data.Conat
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.Properties
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Congruence properties

++-leftCong : ∀ {xs ys zs} → xs ≡ ys → xs ++ zs ≡ ys ++ zs
++-leftCong refl = refl

++-rightCong : ∀ {xs ys zs} → ys ≡ zs → xs ++ ys ≡ xs ++ zs
++-rightCong refl = refl

mapCong₂ : ∀ {f xs ys} → xs ≡ ys → map f xs ≡ map f ys
mapCong₂ refl = refl

revCong₁ : ∀ {xs ys zs} → xs ≡ ys → rev xs zs ≡ rev ys zs
revCong₁ refl = refl

revCong₂ : ∀ {xs ys zs} → ys ≡ zs → rev xs ys ≡ rev xs zs
revCong₂ refl = refl

reverseCong : ∀ {xs ys} → xs ≡ ys → reverse xs ≡ reverse ys
reverseCong refl = refl

reverse'Cong : ∀ {xs ys} → xs ≡ ys → reverse' xs ≡ reverse' ys
reverse'Cong refl = refl

lengthCong : ∀ {xs ys} → xs ≡ ys → length xs ≡ length ys
lengthCong refl = refl

------------------------------------------------------------------------------
-- Totality properties

lengthList-N : ∀ {xs} → List xs → N (length xs)
lengthList-N lnil               = subst N (sym length-[]) nzero
lengthList-N (lcons x {xs} Lxs) =
  subst N (sym (length-∷ x xs)) (nsucc (lengthList-N Lxs))

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

reverse'-List : ∀ {xs} → List xs → List (reverse' xs)
reverse'-List lnil = subst List (sym reverse'-[]) lnil
reverse'-List (lcons x {xs} Lxs) =
  subst List (sym (reverse'-∷ x xs)) (++-List (reverse'-List Lxs) (lcons x lnil))

-- Length properties

lg-x<lg-x∷xs : ∀ x {xs} → List xs → length xs < length (x ∷ xs)
lg-x<lg-x∷xs x lnil =
  lt (length []) (length (x ∷ []))
    ≡⟨ subst₂ (λ t t' → lt (length []) (length (x ∷ [])) ≡ lt t t')
              length-[]
              (length-∷ x [])
              refl
    ⟩
  lt zero (succ₁ (length []))
    ≡⟨ lt-0S (length []) ⟩
  true ∎

lg-x<lg-x∷xs x (lcons y {xs} Lxs) =
  lt (length (y ∷ xs)) (length (x ∷ y ∷ xs))
    ≡⟨ subst₂ (λ t t' → lt (length (y ∷ xs)) (length (x ∷ y ∷ xs)) ≡ lt t t')
              (length-∷ y xs)
              (length-∷ x (y ∷ xs))
              refl
    ⟩
  lt (succ₁ (length xs)) (succ₁ (length (y ∷ xs)))
    ≡⟨ lt-SS (length xs) (length (y ∷ xs)) ⟩
  lt (length xs) (length (y ∷ xs))
    ≡⟨ lg-x<lg-x∷xs y Lxs ⟩
  true ∎

lg-xs<lg-[]→⊥ : ∀ {xs} → List xs → ¬ (length xs < length [])
lg-xs<lg-[]→⊥ lnil lg-[]<lg-[] = ⊥-elim (0<0→⊥ helper)
  where
  helper : zero < zero
  helper =
    lt zero zero
      ≡⟨ subst₂ (λ t t' → lt zero zero ≡ lt t t')
                (sym length-[])
                (sym length-[])
                refl
      ⟩
    lt (length []) (length [])
      ≡⟨ lg-[]<lg-[] ⟩
    true ∎

lg-xs<lg-[]→⊥ (lcons x {xs} Lxs) lg-x∷xs<lg-[] = ⊥-elim (S<0→⊥ helper)
  where
  helper : succ₁ (length xs) < zero
  helper =
    lt (succ₁ (length xs)) zero
      ≡⟨ subst₂ (λ t t' → lt (succ₁ (length xs)) zero ≡ lt t t')
                (sym (length-∷ x xs))
                (sym length-[])
                refl
      ⟩
    lt (length (x ∷ xs)) (length [])
      ≡⟨ lg-x∷xs<lg-[] ⟩
    true ∎

lg-xs≡∞→lg-x∷xs≡∞ : ∀ x xs → length xs ≡ ∞ → length (x ∷ xs) ≡ ∞
lg-xs≡∞→lg-x∷xs≡∞ x xs h =
  length (x ∷ xs)   ≡⟨ length-∷ x xs ⟩
  succ₁ (length xs) ≡⟨ succCong h ⟩
  succ₁ ∞           ≡⟨ sym ∞-eq ⟩
  ∞                 ∎

-- Append properties

++-leftIdentity : ∀ xs → [] ++ xs ≡ xs
++-leftIdentity = ++-[]

++-rightIdentity : ∀ {xs} → List xs → xs ++ [] ≡ xs
++-rightIdentity lnil               = ++-leftIdentity []
++-rightIdentity (lcons x {xs} Lxs) =
  (x ∷ xs) ++ [] ≡⟨ ++-∷ x xs [] ⟩
  x ∷ (xs ++ []) ≡⟨ ∷-rightCong (++-rightIdentity Lxs) ⟩
  x ∷ xs         ∎

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc lnil ys zs =
  ([] ++ ys) ++ zs ≡⟨ ++-leftCong (++-leftIdentity ys) ⟩
  ys ++ zs         ≡⟨ sym (++-leftIdentity (ys ++ zs)) ⟩
  [] ++ ys ++ zs   ∎

++-assoc (lcons x {xs} Lxs) ys zs =
  ((x ∷ xs) ++ ys) ++ zs ≡⟨ ++-leftCong (++-∷ x xs ys) ⟩
  (x ∷ (xs ++ ys)) ++ zs ≡⟨ ++-∷ x (xs ++ ys) zs ⟩
  x ∷ ((xs ++ ys) ++ zs) ≡⟨ ∷-rightCong (++-assoc Lxs ys zs) ⟩
  x ∷ (xs ++ ys ++ zs)   ≡⟨ sym (++-∷ x xs (ys ++ zs)) ⟩
  (x ∷ xs) ++ ys ++ zs   ∎

-- Map properties

map-++ : ∀ f {xs} → List xs → ∀ ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f lnil ys =
  map f ([] ++ ys)     ≡⟨ mapCong₂ (++-leftIdentity ys) ⟩
  map f ys             ≡⟨ sym (++-leftIdentity (map f ys)) ⟩
  [] ++ map f ys       ≡⟨ ++-leftCong (sym (map-[] f)) ⟩
  map f [] ++ map f ys ∎

map-++ f (lcons x {xs} Lxs) ys =
  map f ((x ∷ xs) ++ ys)         ≡⟨ mapCong₂ (++-∷ x xs ys) ⟩
  map f (x ∷ xs ++ ys)           ≡⟨ map-∷ f x (xs ++ ys) ⟩
  f · x ∷ map f (xs ++ ys)       ≡⟨ ∷-rightCong (map-++ f Lxs ys) ⟩
  f · x ∷ (map f xs ++ map f ys) ≡⟨ sym (++-∷ (f · x) (map f xs) (map f ys)) ⟩
  (f · x ∷ map f xs) ++ map f ys ≡⟨ ++-leftCong (sym (map-∷ f x xs)) ⟩
  map f (x ∷ xs) ++ map f ys     ∎

map≡[] : ∀ {f xs} → List xs → map f xs ≡ [] → xs ≡ []
map≡[] lnil                   h = refl
map≡[] {f} (lcons x {xs} Lxs) h = ⊥-elim ([]≢cons (trans (sym h) (map-∷ f x xs)))

-- Reverse properties

reverse-[x]≡[x] : ∀ x → reverse (x ∷ []) ≡ x ∷ []
reverse-[x]≡[x] x =
  rev (x ∷ []) [] ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ []) ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []          ∎

rev-++ : ∀ {xs} → List xs → ∀ ys → rev xs ys ≡ rev xs [] ++ ys
rev-++ lnil ys =
  rev [] ys       ≡⟨ rev-[] ys ⟩
  ys              ≡⟨ sym (++-leftIdentity ys) ⟩
  [] ++ ys        ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  rev [] [] ++ ys ∎

rev-++ (lcons x {xs} Lxs) ys =
  rev (x ∷ xs) ys
    ≡⟨ rev-∷ x xs ys ⟩
  rev xs (x ∷ ys)
    ≡⟨ rev-++ Lxs (x ∷ ys) ⟩
  rev xs [] ++ x ∷ ys
    ≡⟨ subst (λ t → rev xs [] ++ x ∷ ys ≡ rev xs [] ++ t)
             (sym (
               (x ∷ []) ++ ys  ≡⟨ ++-∷ x [] ys ⟩
                x ∷ ([] ++ ys) ≡⟨ ∷-rightCong (++-leftIdentity ys) ⟩
                x ∷ ys         ∎
               )
             )
             refl
    ⟩
  rev xs [] ++ (x ∷ []) ++ ys
    ≡⟨ sym (++-assoc (rev-List Lxs lnil) (x ∷ []) ys) ⟩
  (rev xs [] ++ (x ∷ [])) ++ ys
    ≡⟨ ++-leftCong (sym (rev-++ Lxs (x ∷ []))) ⟩
  rev xs (x ∷ []) ++ ys
    ≡⟨ ++-leftCong (sym (rev-∷ x xs [])) ⟩
  rev (x ∷ xs) [] ++ ys ∎

reverse-++ : ∀ {xs ys} → List xs → List ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} lnil Lys =
  reverse ([] ++ ys)       ≡⟨ reverseCong (++-leftIdentity ys) ⟩
  reverse ys               ≡⟨ sym (++-rightIdentity (reverse-List Lys)) ⟩
  reverse ys ++ []         ≡⟨ ++-rightCong (sym (rev-[] [])) ⟩
  reverse ys ++ reverse [] ∎

reverse-++ (lcons x {xs} Lxs) lnil =
  reverse ((x ∷ xs) ++ [])
    ≡⟨ reverseCong (++-rightIdentity (lcons x Lxs)) ⟩
  reverse (x ∷ xs)
    ≡⟨ sym (++-leftIdentity (reverse (x ∷ xs))) ⟩
  [] ++ reverse (x ∷ xs)
     ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  reverse [] ++ reverse (x ∷ xs) ∎

reverse-++ (lcons x {xs} Lxs) (lcons y {ys} Lys) =
  reverse ((x ∷ xs) ++ y ∷ ys)
    ≡⟨ refl ⟩
  rev ((x ∷ xs) ++ y ∷ ys) []
    ≡⟨ revCong₁ (++-∷ x xs (y ∷ ys)) ⟩
  rev (x ∷ (xs ++ y ∷ ys)) []
    ≡⟨ rev-∷ x (xs ++ y ∷ ys) [] ⟩
  rev (xs ++ y ∷ ys) (x ∷ [])
    ≡⟨ rev-++ (++-List Lxs (lcons y Lys)) (x ∷ []) ⟩
  rev (xs ++ y ∷ ys) [] ++ (x ∷ [])
    ≡⟨ refl ⟩
  reverse (xs ++ y ∷ ys) ++ (x ∷ [])
    ≡⟨ ++-leftCong (reverse-++ Lxs (lcons y Lys)) ⟩
  (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
    ≡⟨ ++-assoc (reverse-List (lcons y Lys)) (reverse xs) (x ∷ []) ⟩
  reverse (y ∷ ys) ++ reverse xs ++ x ∷ []
    ≡⟨ refl ⟩
  reverse (y ∷ ys) ++ rev xs [] ++ x ∷ []
    ≡⟨ ++-rightCong (sym (rev-++ Lxs (x ∷ []))) ⟩
  reverse (y ∷ ys) ++ rev xs (x ∷ [])
    ≡⟨ ++-rightCong (sym (rev-∷ x xs [])) ⟩
  reverse (y ∷ ys) ++ rev (x ∷ xs) []
    ≡⟨ refl ⟩
  reverse (y ∷ ys) ++ reverse (x ∷ xs) ∎

reverse-∷ : ∀ x {ys} → List ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ x lnil =
  rev (x ∷ []) []     ≡⟨ rev-∷ x [] [] ⟩
  rev [] (x ∷ [])     ≡⟨ rev-[] (x ∷ []) ⟩
  x ∷ []              ≡⟨ sym (++-leftIdentity (x ∷ [])) ⟩
  [] ++ x ∷ []        ≡⟨ ++-leftCong (sym (rev-[] [])) ⟩
  rev [] [] ++ x ∷ [] ∎

reverse-∷ x (lcons y {ys} Lys) = sym prf
  where
  prf : reverse (y ∷ ys) ++ x ∷ [] ≡ reverse (x ∷ y ∷ ys)
  prf =
    reverse (y ∷ ys) ++ x ∷ []
      ≡⟨ ++-rightCong (sym (reverse-[x]≡[x] x)) ⟩
    (reverse (y ∷ ys) ++ reverse (x ∷ []))
      ≡⟨ sym (reverse-++ (lcons x lnil) (lcons y Lys)) ⟩
    reverse ((x ∷ []) ++ (y ∷ ys))
      ≡⟨ reverseCong (++-∷ x [] (y ∷ ys)) ⟩
    reverse (x ∷ ([] ++ (y ∷ ys)))
      ≡⟨ reverseCong (∷-rightCong (++-leftIdentity (y ∷ ys))) ⟩
    reverse (x ∷ y ∷ ys) ∎

reverse'-involutive-helper : ∀ x {ys} → List ys →
                             reverse' (ys ++ x ∷ []) ≡ x ∷ reverse' ys
reverse'-involutive-helper x lnil =
  reverse' ([] ++ x ∷ []) ≡⟨ reverse'Cong (++-[] (x ∷ [])) ⟩
  reverse' (x ∷ [])       ≡⟨ reverse'-∷ x [] ⟩
  reverse' [] ++ x ∷ []   ≡⟨ ++-leftCong reverse'-[] ⟩
  [] ++ x ∷ []            ≡⟨ ++-[] (x ∷ []) ⟩
  x ∷ []                  ≡⟨ ∷-rightCong (sym reverse'-[]) ⟩
  x ∷ reverse' []         ∎

reverse'-involutive-helper x (lcons y {ys} Lys) =
  reverse' ((y ∷ ys) ++ x ∷ [])
    ≡⟨ reverse'Cong (++-∷ y ys (x ∷ [])) ⟩
  reverse' (y ∷ ys ++ x ∷ [])
    ≡⟨ reverse'-∷ y (ys ++ x ∷ []) ⟩
  reverse' (ys ++ x ∷ []) ++ y ∷ []
    ≡⟨ ++-leftCong (reverse'-involutive-helper x Lys) ⟩
  (x ∷ reverse' ys) ++ (y ∷ [])
    ≡⟨ ++-∷ x (reverse' ys) (y ∷ []) ⟩
  x ∷ (reverse' ys ++ y ∷ [])
    ≡⟨ ∷-rightCong (sym (reverse'-∷ y ys)) ⟩
  x ∷ reverse' (y ∷ ys) ∎

-- Adapted from (Bird and Wadler, 1988 §5.4.2).
reverse'-involutive : ∀ {xs} → List xs → reverse' (reverse' xs) ≡ xs
reverse'-involutive lnil =
  reverse' (reverse' []) ≡⟨ reverse'Cong reverse'-[] ⟩
  reverse' []            ≡⟨ reverse'-[] ⟩
  []                     ∎

reverse'-involutive (lcons x {xs} Lxs) =
  reverse' (reverse' (x ∷ xs))
    ≡⟨ reverse'Cong (reverse'-∷ x xs) ⟩
  reverse' (reverse' xs ++ (x ∷ []))
    ≡⟨ reverse'-involutive-helper x (reverse'-List Lxs) ⟩
  x ∷ reverse' (reverse' xs)
    ≡⟨ ∷-rightCong (reverse'-involutive Lxs) ⟩
  x ∷ xs ∎

------------------------------------------------------------------------------
-- References

-- Bird, R. and Wadler, P. (1988). Introduction to Functional
-- Programming. Prentice Hall International.
