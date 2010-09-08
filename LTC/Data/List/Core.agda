------------------------------------------------------------------------------
-- Lists (some core definitions)
------------------------------------------------------------------------------

-- The definitions in this file are reexported by LTC.Data.List

module LTC.Data.List.Core where

open import LTC.Minimal.Core using ( D )

infixr 5 _∷_

------------------------------------------------------------------------------
-- List terms
postulate
  []   : D
  _∷_  : D → D → D
