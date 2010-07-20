------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas
------------------------------------------------------------------------------

module FOL.Monad ( T ) where

-- Haskell imports
import Control.Monad.Trans.Error ( ErrorT )
import Control.Monad.Trans.State ( StateT )

-- Local imports
import Common ( Vars )
import Reports ( R )

------------------------------------------------------------------------------
-- The translation monad from Agda types to FOL formulas.
type T = ErrorT String (StateT Vars R)
