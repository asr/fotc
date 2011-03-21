------------------------------------------------------------------------------
-- We don't translate schemas with predicates symbols with arity
-- greater than or equal to five used in logical schemas
------------------------------------------------------------------------------

module Test.Fail.SchemasP5 where

-- Error message:
-- agda2atp: The translation of predicates symbols with arity greater than or equal to five (used in logical schemas) is not implemented

postulate
    D   : Set
    _≡_ : D → D → Set

postulate
   P₅-refl : {P₅ : D → D → D → D → D → Set} →
             {v w x y z : D} →
             P₅ v w x y z → P₅ v w x y z
{-# ATP prove P₅-refl #-}
