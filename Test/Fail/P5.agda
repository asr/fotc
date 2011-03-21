------------------------------------------------------------------------------
-- We don't translate predicates symbols with arity greater than or
-- equal to five
------------------------------------------------------------------------------

module Test.Fail.P5 where

-- Error message:
-- agda2atp: The translation of predicates symbols with arity greater than or equal to five is not implemented

postulate
    D   : Set
    _≡_ : D → D → Set
    P₅  : D → D → D → D → D → Set

postulate
   P₅-refl : {v w x y z : D} → P₅ v w x y z → P₅ v w x y z
{-# ATP prove P₅-refl #-}
