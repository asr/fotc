------------------------------------------------------------------------------
-- Pretty printer for TPTP
------------------------------------------------------------------------------

module TPTP.Pretty where

-- Haskell imports
import Data.Char ( isAlphaNum, ord )

-- Agda library imports
import Agda.Syntax.Abstract ( Name, ModuleName(..), QName(..))

-- Local import
import FOL.FOL2TPTP
import TPTP.Types ( AnnotatedFormula(..), RoleTPTP(..) )

type TPTP = String

class PrettyTPTP a where
    prettyTPTP :: a -> TPTP

instance PrettyTPTP RoleTPTP where
    prettyTPTP AxiomTPTP      = "axiom"
    prettyTPTP ConjectureTPTP = "conjecture"

instance PrettyTPTP Char where
    prettyTPTP c | isAlphaNum c = [c]
                 | otherwise    = show $ ord c

instance PrettyTPTP Name where
    prettyTPTP name = concat $ map prettyTPTP $ show name

instance PrettyTPTP ModuleName where
    prettyTPTP (MName names) = concat $ map prettyTPTP names

instance PrettyTPTP QName where
    prettyTPTP (QName moduleName name) =
        "agda" ++ prettyTPTP moduleName ++ "_" ++ prettyTPTP name

instance PrettyTPTP AnnotatedFormula where
    prettyTPTP (AF qName roleTPTP formula) =
        "fof(" ++
        prettyTPTP qName ++ ", " ++
        prettyTPTP roleTPTP ++ ", " ++
        showTPTP formula ++
        ")." ++ "\n\n"
