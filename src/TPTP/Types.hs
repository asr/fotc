------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types where

-- Agda library imports
import Agda.Syntax.Abstract ( QName )

-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types

------------------------------------------------------------------------------

type NameTPTP = String

data RoleTPTP = AxiomTPTP | ConjectureTPTP

-- The TPTP annotated formulas
data AnnotatedFormula = AF QName RoleTPTP Formula
