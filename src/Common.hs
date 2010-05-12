------------------------------------------------------------------------------
-- Common entities
------------------------------------------------------------------------------

module Common where

-- Haskell imports
import Control.Monad.Trans.Error ( ErrorT )

-- Local imports
import Reports ( R )

------------------------------------------------------------------------------

-- Error handling and report monad.
type ER = ErrorT String R
