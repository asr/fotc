------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types where

-- Agda library imports
import Agda.Syntax.Abstract ( QName )
import Agda.Syntax.Common ( RoleATP )
-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types

------------------------------------------------------------------------------

type NameTPTP = String

-- The TPTP annotated formulas
data AnnotatedFormula = AF QName RoleATP Formula
