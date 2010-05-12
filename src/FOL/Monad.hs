------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas
------------------------------------------------------------------------------

module FOL.Monad where

-- Haskell imports
import Control.Monad.Trans.Reader ( ReaderT )

-- Local imports
import Common ( ER )

------------------------------------------------------------------------------

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.

type Vars = [String]

-- The initial enviroment.
iVarNames :: Vars
iVarNames = []

{-| The translation monad from Agda types to FOL formulas.
-}
type T = ReaderT Vars ER
