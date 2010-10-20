------------------------------------------------------------------------------
-- Bisimulation on LTC streams
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimulation where

open import LTC.Minimal

open import LTC.Data.Stream.Type
  using ( Stream ; consS  -- The LTC stream type.
        )

open import LTC.Minimal.Properties using ( ∷-injective ; ≡-stream )

infix 4 _≈_

------------------------------------------------------------------------------

-- Adapted from [1]. In this paper the authors use the name
-- 'as (R :: R') bs' (p. 310).
-- N.B. This definition should work on streams.

-- [1] Peter Dybjer and Herbert Sander. A functional programming
-- approach to the specification and verification of concurrent
-- systems. Formal Aspects of Computing, 1:303–319, 1989.
BIS : (D → D → Set) → D → D → Set
BIS R xs ys =
  ∃D (λ x' →
  ∃D (λ y' →
  ∃D (λ xs' →
  ∃D (λ ys' →
     x' ≡ y' ∧ R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ y' ∷ ys'))))

-- Because the LTC is a first-order theory, we define a first-order
-- version of the bisimilar relation.
postulate
  _≈_       : D → D → Set
  ≈-GFP-eq₁ : {xs ys : D} → xs ≈ ys → BIS _≈_ xs ys
  ≈-GFP-eq₂ : {xs ys : D} → BIS _≈_ xs ys → xs ≈ ys

-- From the bisimilarity to equality.
-≈-≡ : {xs ys : D} → Stream xs → Stream ys → xs ≈ ys → xs ≡ ys
-≈-≡ (consS x {xs} Sxs) (consS y {ys} Sys) x∷xs≈y∷ys =
  ≡-stream (prf₁ x≡x' y≡y' x'≡y')
           (-≈-≡ Sxs Sys (prf₂ xs≡xs' ys≡ys' xs'≈ys'))
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
    -- TODO: There is a problem with Equinox.
    {-# ATP prove prf₁ #-}

    postulate
      prf₂ : xs ≡ xs' → ys ≡ ys' → xs' ≈ ys' → xs ≈ ys
    -- TODO: There is a problem with Equinox.
    {-# ATP prove prf₂ #-}
