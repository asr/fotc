------------------------------------------------------------------------------
-- Common entities
------------------------------------------------------------------------------

module Common
    ( AllDefinitions
    , iVarNames
    , T
    , TopLevelDefinitions
    , Vars
    )
    where

-- Haskell imports
import Control.Monad.Trans.Error ( ErrorT )
import Control.Monad.Trans.State ( StateT )

-- Agda library imports
import Agda.TypeChecking.Monad.Base ( Definitions )

-- Local imports
import Reports ( R )

------------------------------------------------------------------------------
-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.
type Vars = [String]

-- The initial enviroment.
iVarNames :: Vars
iVarNames = []

-- The translation monad.
type T = ErrorT String (StateT Vars R)

type AllDefinitions      = Definitions
type TopLevelDefinitions = Definitions
