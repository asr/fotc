-- Because a greatest post-fixed point is a fixed point, the
-- bisimilarity relation is also a pre-fixed point of the functor
-- BisimilarityF (see below).


-- TODO: To prove this property using ≈-gfp₂.
postulate
  ≈-gfp₃ : ∀ {xs ys} →
           (∃ λ x' → ∃ λ xs' → ∃ λ ys' → xs' ≈ ys' ∧
                                         xs ≡ x' ∷ xs' ∧
                                         ys ≡ x' ∷ ys') →
           xs ≈ ys
  {-# ATP prove ≈-gfp₃ #-}


xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
xs≈ys→x∷xs≈x∷ys {x} {xs} {ys} xs≈ys =
  ≈-gfp₃ (x , xs , ys , xs≈ys , refl , refl)

postulate
  xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove xs≈ys→x∷xs≈x∷ys #-}
