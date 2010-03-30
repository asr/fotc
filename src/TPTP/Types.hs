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

type NameTPTP = String

data RoleTPTP = AxiomTPTP | ConjectureTPTP | TheoremTPTP

instance Show RoleTPTP where
    show AxiomTPTP      = "axiom"
    show ConjectureTPTP = "conjecture"
    show TheoremTPTP    = "theorem"

-- The TPTP annotated formulas
data AnnotatedFormula = AF String RoleTPTP Formula

instance Show AnnotatedFormula where
    show (AF name roleTPTP formula) =
        "fof(" ++
        name ++ ", " ++
        show roleTPTP ++ ", " ++
        showTPTP formula ++
        ")." ++ "\n\n"
