------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module AxiomaticPA.Equality.Properties where

open import AxiomaticPA.Base

------------------------------------------------------------------------------

refl : ∀ n → n ≣ n
refl n = S₁ (S₅ n) (S₅ n)
{-# ATP hint refl #-}

sym : ∀ {m n} → m ≣ n → n ≣ m
sym {m} = aux S₁ (refl m)
  where
    aux : ∀ {r t} → (t ≣ r → t ≣ t → r ≣ t) → t ≣ t → t ≣ r → r ≣ t
    aux hyp t≣t t≣r = hyp t≣r t≣t
{-# ATP hint sym #-}

trans : ∀ {m n o} → m ≣ n → n ≣ o → m ≣ o
trans m≣n = S₁ (sym m≣n)
{-# ATP hint trans #-}
