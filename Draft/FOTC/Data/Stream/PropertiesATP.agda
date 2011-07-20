------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

module Draft.FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base

open import FOTC.Base.PropertiesATP

open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS {x} {xs} h = subst Stream (sym (∧-proj₂ (∷-injective x∷xs≡e∷es))) Ses
  where
  unfold : ∃ λ e → ∃ λ es → x ∷ xs ≡ e ∷ es ∧ Stream es
  unfold = Stream-gfp₁ h

  e : D
  e = ∃-proj₁ unfold

  es : D
  es = ∃-proj₁ (∃-proj₂ unfold)

  x∷xs≡e∷es : x ∷ xs ≡ e ∷ es
  x∷xs≡e∷es = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold))

  Ses : Stream es
  Ses = ∧-proj₂ (∃-proj₂ (∃-proj₂ unfold))

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P₁ helper₁ (ys , xs≈ys)
                         , Stream-gfp₂ P₂ helper₂ (xs , xs≈ys)
  where
  P₁ : D → Set
  P₁ ws = ∃ λ zs → ws ≈ zs

  postulate
    helper₁ : ∀ {ws} → P₁ ws →
              ∃ (λ w' → ∃ (λ ws' → ws ≡ w' ∷ ws' ∧ P₁ ws'))
  {-# ATP prove helper₁ #-}

  P₂ : D → Set
  P₂ zs = ∃ λ ws → ws ≈ zs

  postulate
    helper₂ : ∀ {zs} → P₂ zs → ∃ (λ z' → ∃ (λ zs' → zs ≡ z' ∷ zs' ∧ P₂ zs'))
  {-# ATP prove helper₂ #-}
