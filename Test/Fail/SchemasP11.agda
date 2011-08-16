------------------------------------------------------------------------------
-- We don't translate schemas with predicates symbols with arity
-- greater than or equal to eleven used in logical schemas
------------------------------------------------------------------------------

module Test.Fail.SchemasP11 where

-- Error message:
-- agda2atp: The translation of predicates symbols with arity greater than or equal to eleven (used in logical schemas) is not implemented

postulate
  D : Set

postulate
  P₁₁-refl : {P₁₁ : D → D → D → D → D → D → D → D → D → D → D → Set} →
             {a b c d e f g h i j k : D} →
             P₁₁ a b c d e f g h i j k → P₁₁ a b c d e f g h i j k
{-# ATP prove P₁₁-refl #-}
