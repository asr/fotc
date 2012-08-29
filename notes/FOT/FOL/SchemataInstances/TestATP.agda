------------------------------------------------------------------------------
-- Testing the use of schemata
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-propositional-functions #-}
{-# OPTIONS --without-K #-}

module FOT.FOL.SchemataInstances.TestATP where

open import FOL.Base

------------------------------------------------------------------------------
-- A schema
-- Current translation: ∀ p q x. app(p,x) → app(q,x).
postulate schema : (A B : D → Set) → ∀ {x} → A x → B x

-- Using the current translation, the ATPs can prove an instance of
-- the schema.
postulate
  d         : D
  A B       : D → Set
  instanceC : A d → B d
{-# ATP prove instanceC schema #-}

instanceI : A d → B d
instanceI Ad = schema A B Ad
