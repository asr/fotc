------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module EtaD where

postulate
  D   : Set
  _≈_ : D → D → Set

data ∃ (A : D → Set) : Set where
  _,_ : (t : D) → A t → ∃ A

P : D → Set
P ws = ∃ (λ zs → ws ≈ zs)
{-# ATP definition P #-}

postulate
  foo : ∀ ws → P ws → ∃ (λ zs → ws ≈ zs)
{-# ATP prove foo #-}
