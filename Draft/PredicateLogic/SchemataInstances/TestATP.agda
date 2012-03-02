------------------------------------------------------------------------------
-- Testing the use of schemata
------------------------------------------------------------------------------

-- Tested with FOT and agda2atp on 07 February 2012.

module Draft.PredicateLogic.SchemataInstances.TestATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

-- A schema
-- Current translation: ∀ p q x. app(p,x) → app(q,x).
postulate schema : (P Q : D → Set) → ∀ {x} → P x → Q x

-- Using the current translation, the ATPs can prove an instance of
-- the schema.
postulate
  d         : D
  P Q       : D → Set
  instanceC : P d → Q d
{-# ATP prove instanceC schema #-}

instanceI : P d → Q d
instanceI Pd = schema P Q Pd
