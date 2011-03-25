------------------------------------------------------------------------------
-- Testing the use of schemas
------------------------------------------------------------------------------

module Draft.PredicateLogic.SchemeInstances.TestATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

-- A scheme
-- Current translation: ∀ p q x. app(p,x) → app(q,x).
postulate
  scheme : (P Q : D → Set){x : D} → P x → Q x

-- Using the current translation, the ATPs can prove an instance of
-- the scheme.
postulate
  d         : D
  P Q       : D → Set
  instanceC : P d → Q d
{-# ATP prove instanceC scheme #-}

-- The interactive proof.
instanceI : P d → Q d
instanceI Pd = scheme P Q Pd
