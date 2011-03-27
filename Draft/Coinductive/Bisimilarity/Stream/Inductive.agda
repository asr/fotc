------------------------------------------------------------------------------
-- Testing the bisimilar relation with inductive (wrong definition) streams
------------------------------------------------------------------------------

module Draft.Bisimilarity.Stream.Inductive where

open import LTC.Base

open import LTC.Base.Properties using ( ∷-injective ; ≡-stream )

open import LTC.Data.Stream.Bisimulation using ( _≈_ ; ≈-GFP-eq₁ ; BISI )

------------------------------------------------------------------------

-- The LTC stream type.
-- Wrong! It should be a coinductive type.
data Stream : D → Set where
  consS : (x : D){xs : D} → (Sxs : Stream xs) → Stream (x ∷ xs)

------------------------------------------------------------------------

-- From the bisimilarity to equality.
-≈-≡ : {xs ys : D} → Stream xs → Stream ys → xs ≈ ys → xs ≡ ys
-≈-≡ (consS x {xs} Sxs) (consS y {ys} Sys) x∷xs≈y∷ys =
  ≡-stream (prf₁ x≡x' y≡y' x'≡y')
           (-≈-≡ Sxs Sys (prf₂ xs≡xs' ys≡ys' xs'≈ys'))
  where

    aux : BISI _≈_ (x ∷ xs) (y ∷ ys)
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
