module Test.Issues.BadProofTermErase where

postulate
  D : Set

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

data ∃ (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃ P

postulate
  something    : D → D → Set
  somethingAll : ∀ a → something a a

foo : ∀ d → d ≡ d
foo d = bar d (d , (somethingAll d))
  where
  unnecesaryR : D → Set
  unnecesaryR e = ∃ λ e' → something e e'

  bar : ∀ f → unnecesaryR f → f ≡ f
  bar f h = barfoo f
    where
    postulate barfoo : ∀ g → g ≡ g
    -- We don't know how to erase the proof term h, therefore the
    -- agda2atp should abort. However, the current version does the
    -- translation.
    {-# ATP prove barfoo #-}
