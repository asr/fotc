------------------------------------------------------------------------------
-- Common entities
------------------------------------------------------------------------------

module Common ( ER, iVarNames, Vars ) where

-- Haskell imports
import Control.Monad.Trans.Error ( ErrorT )

-- Local imports
import Reports ( R )

------------------------------------------------------------------------------
-- Error handling and report monad.
type ER = ErrorT String R

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.
type Vars = [String]

-- The initial enviroment.
iVarNames :: Vars
iVarNames = []
