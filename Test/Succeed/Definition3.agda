------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

module Test.Succeed.Definition3 where

postulate
  D   : Set
  _≡_ : D → D → Set

-- We test the translation of the definition of a 2-ary function.
foo : D → D → D
foo d e = d
{-# ATP definition foo #-}

postulate bar : ∀ d → d ≡ foo d d
{-# ATP prove bar #-}
