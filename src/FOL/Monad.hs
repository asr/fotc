------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas
------------------------------------------------------------------------------

module FOL.Monad where

-- Haskell imports
import Control.Monad.Trans.Error ( ErrorT )
import Control.Monad.Trans.State ( StateT )

-- Local imports
import Reports ( R )

------------------------------------------------------------------------------

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.

type Vars = [String]

-- The initial enviroment.
iVarNames :: Vars
iVarNames = []

{-| The translation monad from Agda types to FOL formulas.
-}
type T = ErrorT String (StateT Vars R)
