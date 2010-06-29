module Test.Fail.Add where

infix  4 _≡_
infixl 6 _+_

postulate
  D      : Set
  zero   : D
  succ   : D → D
  _≡_    : D → D → Set
  _+_    : D → D → D
  +-0x : (d : D) →   zero   + d ≡ d
  +-Sx : (d e : D) → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x #-}
{-# ATP axiom +-Sx #-}

-- The ATPs cannot prove this postulate from the axioms.
postulate
  +-comm : (d e : D) → d + e ≡ e + d
{-# ATP prove +-comm #-}
