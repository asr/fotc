------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Minimal.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  succInjectivity : {d e : D} → succ d ≡ succ e → d ≡ e
{-# ATP prove succInjectivity #-}

