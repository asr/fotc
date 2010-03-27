------------------------------------------------------------------------------
-- The translation monad from Agda EXTERNAL pragmas to TPTP annotated formulas
------------------------------------------------------------------------------

module TPTP.Monad where

-- Haskell imports
import Control.Monad.Trans.State ( State )

-- Local imports
import TPTP.Types

initialNames :: [NameTPTP]
initialNames = []

-- The environmet '[NameTPTP]' represents ...

type N a = State [NameTPTP] a
