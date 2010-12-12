------------------------------------------------------------------------------
-- Test the consistency of LTC.Base
------------------------------------------------------------------------------

-- In the module LTC.Base we declare Agda postulates as FOL axioms. We
-- test if it is possible to prove an unprovable theorem from these
-- axioms.

module LTC.Base.ConsistencyTest where

open import LTC.Base

------------------------------------------------------------------------------

postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
