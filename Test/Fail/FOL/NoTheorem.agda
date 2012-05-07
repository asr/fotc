------------------------------------------------------------------------------
-- Error message when the ATPs could not prove a conjecture
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Fail.FOL.NoTheorem where

-- Error message (using the option --unproved-conjecture-error):
-- Error: The ATP(s) did not prove the conjecture in /tmp/Test.Fail.NoTheorem.43-comm_26.tptp

infix  4 _≡_
infixl 6 _+_

postulate
  D      : Set
  zero   : D
  succ   : D → D
  _≡_    : D → D → Set
  _+_    : D → D → D
  +-0x   : (d : D) → zero + d     ≡ d
  +-Sx   : (d e : D) → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x #-}
{-# ATP axiom +-Sx #-}

-- The ATPs should not prove this postulate.
postulate
  +-comm : (d e : D) → d + e ≡ e + d
-- E 1.5 success (SZS status CounterSatisfiable).
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout.
-- Metis 2.3 (release 20100920) success (SZS status CounterSatisfiable).
-- Vampire 0.6 (revision 903): Refutation not found!
{-# ATP prove +-comm #-}
