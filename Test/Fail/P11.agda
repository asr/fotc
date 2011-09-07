------------------------------------------------------------------------------
-- We don't translate predicates symbols with arity greater than or
-- equal to eleven
------------------------------------------------------------------------------

module Test.Fail.P11 where

-- Error: The translation of predicates symbols with arity greater than or equal to eleven as Test.Fail.P11.P₁₁ is not implemented

postulate
  D   : Set
  P₁₁ : D → D → D → D → D → D → D → D → D → D → D → Set

postulate
  P₁₁-refl : {a b c d e f g h i j k : D} →
             P₁₁ a b c d e f g h i j k → P₁₁ a b c d e f g h i j k
{-# ATP prove P₁₁-refl #-}
