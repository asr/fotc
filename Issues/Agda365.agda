------------------------------------------------------------------------------
-- Issue in the translation inspired by the Agda issue 365
------------------------------------------------------------------------------

module Issues.Agda365 where

postulate
  D   : Set
  _≡_ : D → D → Set

foo : D → D
-- foo d = d  -- Works!
foo = λ d → d  -- Doesn't work!
{-# ATP definition foo #-}

postulate bar : ∀ d → d ≡ foo d
{-# ATP prove bar #-}
