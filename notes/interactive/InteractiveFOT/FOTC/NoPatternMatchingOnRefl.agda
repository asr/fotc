------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.NoPatternMatchingOnRefl where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List

open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.Conat
open import Interactive.FOTC.Data.Conat.Equality.Type
  renaming
    ( _≈_ to _≈N_
    ; ≈-coind to ≈N-coind
    )
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Stream.Type

open import Interactive.FOTC.Program.McCarthy91.McCarthy91

open import Interactive.FOTC.Relation.Binary.Bisimilarity.Properties
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- From FOTC.Base.PropertiesI

-- Congruence properties

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong {a} {c = c} h = subst (λ t → a · c ≡ t · c) h refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong {a} {b} h = subst (λ t → a · b ≡ a · t) h refl

·-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a · c ≡ b · d
·-cong {a} {c = c} h₁ h₂ = subst₂ (λ t₁ t₂ → a · c ≡ t₁ · t₂) h₁ h₂ refl

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong {m} h = subst (λ t → succ₁ m ≡ succ₁ t) h refl

predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
predCong {m} h = subst (λ t → pred₁ m ≡ pred₁ t) h refl

ifCong₁ : ∀ {b b' t t'} → b ≡ b' →
         (if b then t else t') ≡ (if b' then t else t')
ifCong₁ {b} {t = t} {t'} h =
  subst (λ x → (if b then t else t') ≡ (if x then t else t')) h refl

ifCong₂ : ∀ {b t₁ t₂ t} → t₁ ≡ t₂ →
         (if b then t₁ else t) ≡ (if b then t₂ else t)
ifCong₂ {b} {t₁} {t = t} h =
  subst (λ x → (if b then t₁ else t) ≡ (if b then x else t)) h refl

ifCong₃ : ∀ {b t t₁ t₂} → t₁ ≡ t₂ →
          (if b then t else t₁) ≡ (if b then t else t₂)
ifCong₃ {b} {t} {t₁} h =
  subst (λ x → (if b then t else t₁) ≡ (if b then t else x)) h refl

------------------------------------------------------------------------------
-- From FOTC.Base.List.PropertiesI

-- Congruence properties

∷-leftCong : ∀ {x y xs} → x ≡ y → x ∷ xs ≡ y ∷ xs
∷-leftCong {x} {xs = xs} h = subst (λ t → x ∷ xs ≡ t ∷ xs) h refl

∷-rightCong : ∀ {x xs ys} → xs ≡ ys → x ∷ xs ≡ x ∷ ys
∷-rightCong {x}{xs} h = subst (λ t → x ∷ xs ≡ x ∷ t) h refl

∷-Cong : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
∷-Cong {x} {xs = xs} h₁ h₂ = subst₂ (λ t₁ t₂ → x ∷ xs ≡ t₁ ∷ t₂) h₁ h₂ refl

headCong : ∀ {xs ys} → xs ≡ ys → head₁ xs ≡ head₁ ys
headCong {xs} h = subst (λ t → head₁ xs ≡ head₁ t) h refl

tailCong : ∀ {xs ys} → xs ≡ ys → tail₁ xs ≡ tail₁ ys
tailCong {xs} h = subst (λ t → tail₁ xs ≡ tail₁ t) h refl

------------------------------------------------------------------------------
-- From FOTC.Data.Bool.PropertiesI

-- Congruence properties

&&-leftCong : ∀ {a b c} → a ≡ b → a && c ≡ b && c
&&-leftCong {a} {c = c} h = subst (λ t → a && c ≡ t && c) h refl

&&-rightCong : ∀ {a b c} → b ≡ c → a && b ≡ a && c
&&-rightCong {a} {b} h = subst (λ t → a && b ≡ a && t) h refl

&&-cong : ∀ {a b c d } → a ≡ c → b ≡ d → a && b ≡ c && d
&&-cong {a} {b} h₁ h₂ = subst₂ (λ t₁ t₂ → a && b ≡ t₁ && t₂) h₁ h₂ refl

notCong : ∀ {a b} → a ≡ b → not a ≡ not b
notCong {a} h = subst (λ t → not a ≡ not t) h refl

------------------------------------------------------------------------------
-- FOTC.Data.Conat.Equality.PropertiesI

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b

  h₁ : ∀ {a b} → R a b →
       a ≡ zero ∧ b ≡ zero
         ∨ (∃[ a' ] ∃[ b' ] a ≡ succ₁ a' ∧ b ≡ succ₁ b' ∧ R a' b')
  h₁ (Ca , Cb , h) with Conat-out Ca
  ... | inj₁ prf              = inj₁ (prf , trans (sym h) prf)
  ... | inj₂ (a' , prf , Ca') =
    inj₂ (a' , a' , prf , trans (sym h) prf , (Ca' , Ca' , refl))

  h₂ : R n n
  h₂ = Cn , Cn , refl

≡→≈ : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈ {m} Cm _ h = subst (_≈N_ m) h (≈N-refl Cm)

------------------------------------------------------------------------------
-- FOTC.Data.List.PropertiesI

-- Congruence properties

++-leftCong : ∀ {xs ys zs} → xs ≡ ys → xs ++ zs ≡ ys ++ zs
++-leftCong {xs} {zs = zs} h = subst (λ t → xs ++ zs ≡ t ++ zs) h refl

++-rightCong : ∀ {xs ys zs} → ys ≡ zs → xs ++ ys ≡ xs ++ zs
++-rightCong {xs} {ys} h = subst (λ t → xs ++ ys ≡ xs ++ t) h refl

mapCong₂ : ∀ {f xs ys} → xs ≡ ys → map f xs ≡ map f ys
mapCong₂ {f} {xs} h = subst (λ t → map f xs ≡ map f t) h refl

revCong₁ : ∀ {xs ys zs} → xs ≡ ys → rev xs zs ≡ rev ys zs
revCong₁ {xs} {zs = zs} h = subst (λ t → rev xs zs ≡ rev t zs) h refl

revCong₂ : ∀ {xs ys zs} → ys ≡ zs → rev xs ys ≡ rev xs zs
revCong₂ {xs} {ys} h = subst (λ t → rev xs ys ≡ rev xs t) h refl

reverseCong : ∀ {xs ys} → xs ≡ ys → reverse xs ≡ reverse ys
reverseCong {xs} h = subst (λ t → reverse xs ≡ reverse t) h refl

lengthCong : ∀ {xs ys} → xs ≡ ys → length xs ≡ length ys
lengthCong {xs} h = subst (λ t → length xs ≡ length t) h refl

------------------------------------------------------------------------------
-- From FOTC.Data.Nat.Inequalities.PropertiesI

-- Congruence properties

leLeftCong : ∀ {m n o} → m ≡ n → le m o ≡ le n o
leLeftCong {m} {o = o} h = subst (λ t → le m o ≡ le t o) h refl

ltLeftCong : ∀ {m n o} → m ≡ n → lt m o ≡ lt n o
ltLeftCong {m} {o = o} h = subst (λ t → lt m o ≡ lt t o) h refl

ltRightCong : ∀ {m n o} → n ≡ o → lt m n ≡ lt m o
ltRightCong {m} {n} h = subst (λ t → lt m n ≡ lt m t) h refl

ltCong : ∀ {m₁ n₁ m₂ n₂} → m₁ ≡ m₂ → n₁ ≡ n₂ → lt m₁ n₁ ≡ lt m₂ n₂
ltCong {m₁} {n₁} h₁ h₂ = subst₂ (λ t₁ t₂ → lt m₁ n₁ ≡ lt t₁ t₂) h₁ h₂ refl

------------------------------------------------------------------------------
-- From FOTC.Data.Nat.PropertiesI

-- Congruence properties

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong {m} {o = o} h = subst (λ t → m + o ≡ t + o) h refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong {m} {n} h = subst (λ t → m + n ≡ m + t) h refl

∸-leftCong : ∀ {m n o} → m ≡ n → m ∸ o ≡ n ∸ o
∸-leftCong {m} {o = o} h = subst (λ t → m ∸ o ≡ t ∸ o) h refl

∸-rightCong : ∀ {m n o} → n ≡ o → m ∸ n ≡ m ∸ o
∸-rightCong {m} {n} h = subst (λ t → m ∸ n ≡ m ∸ t) h refl

*-leftCong : ∀ {m n o} → m ≡ n → m * o ≡ n * o
*-leftCong {m} {o = o} h = subst (λ t → m * o ≡ t * o) h refl

*-rightCong : ∀ {m n o} → n ≡ o → m * n ≡ m * o
*-rightCong {m} {n} h = subst (λ t → m * n ≡ m * t) h refl

------------------------------------------------------------------------------
-- From InteractiveFOT.FOTC.Data.Stream.Equality.PropertiesI where

stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
stream-≡→≈ {xs} Sxs _ h = subst (_≈_ xs) h (≈-refl Sxs)

------------------------------------------------------------------------------
-- From FOTC.Program.McCarthy91.AuxiliaryPropertiesATP

f₉₁-x≡y : ∀ {m n o} → f₉₁ m ≡ n → o ≡ m → f₉₁ o ≡ n
f₉₁-x≡y {n = n} h₁ h₂ = subst (λ t → f₉₁ t ≡ n) (sym h₂) h₁
