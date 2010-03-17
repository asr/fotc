------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types where

-- Agda library imports
-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types
import FOL.FOL2TPTP

------------------------------------------------------------------------------

data RoleTPTP = AxiomTPTP | ConjectureTPTP

instance Show RoleTPTP where
    show AxiomTPTP      = "axiom"
    show ConjectureTPTP = "conjecture"

data LineTPTP = AFormula String RoleTPTP Formula

instance Show LineTPTP where
    show (AFormula name role formula) =
        "fof(" ++
        show name ++ ", " ++
        show role ++ ", " ++
        showTPTP formula ++
        ")." ++ "\n"
