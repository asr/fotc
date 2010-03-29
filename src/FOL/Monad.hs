------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas
------------------------------------------------------------------------------

module FOL.Monad where

-- Haskell imports
import Control.Monad.Trans.Reader ( ReaderT )

-- Local imports
import Reports ( R )

------------------------------------------------------------------------------

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.

type Vars = [String]

initialVars :: Vars
initialVars = []

{-| The translation monad from Agda types to FOL formulas.
-}
type T a = ReaderT Vars R a
