------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types where

-- Agda library imports
import Agda.Syntax.Abstract ( QName )

-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types
import FOL.FOL2TPTP

------------------------------------------------------------------------------

type NameTPTP = String

data RoleTPTP = AxiomTPTP | ConjectureTPTP

instance Show RoleTPTP where
    show AxiomTPTP      = "axiom"
    show ConjectureTPTP = "conjecture"

-- The TPTP annotated formulas
data AnnotatedFormula = AF QName RoleTPTP Formula

instance Show AnnotatedFormula where
    show (AF qName roleTPTP formula) =
        "fof(" ++
        show qName ++ ", " ++
        show roleTPTP ++ ", " ++
        showTPTP formula ++
        ")." ++ "\n\n"
