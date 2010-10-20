------------------------------------------------------------------------------
-- Testing the bisimilar relation using co-inductive streams
------------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Draft.Bisimilarity.Stream.Coinductive where

open import LTC.Minimal

open import LTC.Minimal.Properties using ( ∷-injective ; ≡-stream )

open import LTC.Data.Stream.Bisimulation hiding ( -≈-≡ )

------------------------------------------------------------------------------
-- Universe levels (from the standard library)

data Level : Set where
  zeroL : Level
  sucL  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zeroL  #-}
{-# BUILTIN LEVELSUC  sucL   #-}

-- Maximum.

infixl 6 _⊔_

_⊔_ : Level → Level → Level
zeroL  ⊔ j      = j
sucL i ⊔ zeroL  = sucL i
sucL i ⊔ sucL j = sucL (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

------------------------------------------------------------------------
-- Basic types related to coinduction (from the standard library)

-- A type used to make recursive arguments coinductive

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

------------------------------------------------------------------------
-- Co-inductive streams

-- The LTC stream type.
data Stream : D → Set where
  consS : (x : D){xs : D} → (Sxs : ∞ (Stream xs)) → Stream (x ∷ xs)

------------------------------------------------------------------------
-- The bisimilar and the equality relation.
-≈-≡ : {xs ys : D} → Stream xs → Stream ys → xs ≈ ys → xs ≡ ys
-≈-≡ (consS x {xs} Sxs) (consS y {ys} Sys) x∷xs≈y∷ys =
  ≡-stream (prf₁ x≡x' y≡y' x'≡y')
           (-≈-≡ (♭ Sxs) (♭ Sys) (prf₂ xs≡xs' ys≡ys' xs'≈ys'))
  where

    aux : BIS _≈_ (x ∷ xs) (y ∷ ys)
    aux = ≈-GFP-eq₁ x∷xs≈y∷ys

    x' : D
    x' = ∃D-proj₁ aux

    y' : D
    y' = ∃D-proj₁ (∃D-proj₂ aux)

    xs' : D
    xs' = ∃D-proj₁ (∃D-proj₂ (∃D-proj₂ aux))

    ys' : D
    ys' = ∃D-proj₁ (∃D-proj₂ (∃D-proj₂ (∃D-proj₂ aux)))

    x'≡y' : x' ≡ y'
    x'≡y' = ∧-proj₁ (∃D-proj₂
                    (∃D-proj₂
                    (∃D-proj₂
                    (∃D-proj₂ aux))))

    xs'≈ys' : xs' ≈ ys'
    xs'≈ys' = ∧-proj₁ (∧-proj₂ (∃D-proj₂
                               (∃D-proj₂
                               (∃D-proj₂
                               (∃D-proj₂ aux)))))

    x∷xs≡x'∷xs' : x ∷ xs ≡ x' ∷ xs'
    x∷xs≡x'∷xs' =
      ∧-proj₁ (∧-proj₂ (∧-proj₂ (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂ aux))))))

    y∷ys≡y'∷ys' : y ∷ ys ≡ y' ∷ ys'
    y∷ys≡y'∷ys' =
      ∧-proj₂ (∧-proj₂ (∧-proj₂ (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂ aux))))))

    x≡x' : x ≡ x'
    x≡x' = ∧-proj₁ (∷-injective x∷xs≡x'∷xs')

    y≡y' : y ≡ y'
    y≡y' = ∧-proj₁ (∷-injective y∷ys≡y'∷ys')

    xs≡xs' : xs ≡ xs'
    xs≡xs' = ∧-proj₂ (∷-injective x∷xs≡x'∷xs')

    ys≡ys' : ys ≡ ys'
    ys≡ys' = ∧-proj₂ (∷-injective y∷ys≡y'∷ys')

    postulate
      prf₁ : x ≡ x' → y ≡ y' → x' ≡ y' → x ≡ y
    {-# ATP prove prf₁ #-}

    postulate
      prf₂ : xs ≡ xs' → ys ≡ ys' → xs' ≈ ys' → xs ≈ ys
    {-# ATP prove prf₂ #-}
