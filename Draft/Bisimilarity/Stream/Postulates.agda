------------------------------------------------------------------------------
-- Testing the bisimilar relation with streams via postulates
------------------------------------------------------------------------------

module Draft.Bisimilarity.Stream.Postulates where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

import Lib.Relation.Binary.EqReasoning
open module Postulates-ER =
  Lib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import LTC.Minimal.Properties using ( ∷-injective ; ≡-stream )

open import LTC.Data.Stream.Bisimulation hiding ( -≈-≡ )

------------------------------------------------------------------------
-- The LTC stream type.

postulate
  Stream   : D → Set
  consS    : (x : D){xs : D} → Stream xs → Stream (x ∷ xs)
  invConsS : (x : D){xs : D} → Stream (x ∷ xs) → Stream xs

------------------------------------------------------------------------
-- The bisimilar and the equality relation.
-≈-≡ : {xs ys : D} → Stream xs → Stream ys → xs ≈ ys → xs ≡ ys
-≈-≡ {xs} {ys} Sxs Sys xs≈ys =
  begin
    xs       ≡⟨ xs≡x'∷xs' ⟩
    x' ∷ xs' ≡⟨ ≡-stream x'≡y' (-≈-≡ Sxs' Sys' xs'≈ys') ⟩
    y' ∷ ys' ≡⟨ sym ys≡y'∷ys' ⟩
    ys
  ∎

  where
    aux : BIS _≈_ xs ys
    aux = ≈-GFP-eq₁ xs≈ys

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

    xs≡x'∷xs' : xs ≡ x' ∷ xs'
    xs≡x'∷xs' =
      ∧-proj₁ (∧-proj₂ (∧-proj₂ (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂ aux))))))

    ys≡y'∷ys' : ys ≡ y' ∷ ys'
    ys≡y'∷ys' =
      ∧-proj₂ (∧-proj₂ (∧-proj₂ (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂
                                (∃D-proj₂ aux))))))

    Sxs' : Stream xs'
    Sxs' = invConsS x' (subst (λ t → Stream t) xs≡x'∷xs' Sxs)

    Sys' : Stream ys'
    Sys' = invConsS y' (subst (λ t → Stream t) ys≡y'∷ys' Sys)
