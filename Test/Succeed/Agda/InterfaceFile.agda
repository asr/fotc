module Test.Succeed.Agda.InterfaceFile where

{-
After the Agda patches

Thu Sep  9 08:41:13 COT 2010  andreas.abel@ifi.lmu.de

  * Added an extra argument to Internal.ConP to hold the type of
    record patterns.  Does nothing yet.

Thu Sep  9 08:42:06 COT 2010  andreas.abel@ifi.lmu.de
  * Forgot this one module.  (still Internal.ConP)

The agda2atp tool could not read the interface generated for this file
due to an Agda bug.
-}

module Bad where

data N : Set where
  zero : N
  succ : N → N

indN : (P : N → Set) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n
indN P P0 h zero     = P0
indN P P0 h (succ n) = h n (indN P P0 h n)
