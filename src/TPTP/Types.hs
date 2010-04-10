------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types where

-- Agda library imports
import Agda.Syntax.Abstract ( QName )
import Agda.Syntax.Common ( RoleATP )
-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types ( FormulaFOL )

------------------------------------------------------------------------------

-- The TPTP annotated formulas.
-- N.B. The annotated formulas are not in TPTP syntax. We get this syntax via
-- a pretty-printer.
data AF = AF QName RoleATP FormulaFOL
