------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas
------------------------------------------------------------------------------

module FOL.Monad where

-- Haskell imports
import Control.Monad.Trans.Reader ( ReaderT )

-- Local imports
import Options ( Options )

------------------------------------------------------------------------------

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.

type Vars = [String]

initialVars :: Vars
initialVars = []

{-| The translation monad from Agda types to FOL formulas.
-}
type T a = ReaderT (Options, Vars) IO a
