------------------------------------------------------------------------------
-- Translation of projection-like functions

-- 2012-02-23: The function P is not considered a projection-like
-- function after the patch:

--   Tue Feb 21 11:41:08 COT 2012  Nils Anders Danielsson <nils.anders.danielsson@gmail.com>
--   * The positivity checker (and more) is now only run once per mutual block.

-- 2011-09-23: From the Agda mailing list
-- Subject: Compiler internals for projection functions
-- There is some additional information about this issue.

-- 2011-09-19: Maybe the information in the issue 465 (Missing
-- patterns in funClauses) is useful.

------------------------------------------------------------------------------

module Test.Succeed.ProjectionLikeFunction where

postulate
  D    : Set
  _≡_  : D → D → Set
  N    : D → Set

foo : ∀ {n} → N n → D
foo {n} Nn = n
  where
  P : D → Set
  P i = i ≡ i
  {-# ATP definition P #-}

  postulate bar : P n
  {-# ATP prove bar #-}
