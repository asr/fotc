------------------------------------------------------------------------------
-- Pretty printer for TPTP
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TPTP.Pretty where

-- Haskell imports
import Data.Char
import Data.List.HT ( replace )
-- Agda library imports
import Agda.Syntax.Common ( NameId, RoleATP(..) )
import Agda.Syntax.Abstract.Name ( Name(nameId), QName(..))
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local import
import FOL.Types
import TPTP.Types ( AnnotatedFormula(..) )
#include "../undefined.h"

------------------------------------------------------------------------------

type TPTP = String

class PrettyTPTP a where
    prettyTPTP :: a -> TPTP

changeCaseFirstSymbol :: TPTP -> (Char -> Char) -> TPTP
changeCaseFirstSymbol []       _ = __IMPOSSIBLE__
changeCaseFirstSymbol (x : xs) f = f x : xs

changeToUpper :: TPTP -> TPTP
changeToUpper name = changeCaseFirstSymbol (prettyTPTP name) toUpper

changeToLower :: TPTP -> TPTP
changeToLower name = changeCaseFirstSymbol (prettyTPTP name) toLower

------------------------------------------------------------------------------
-- Pretty-printer for Haskell types

instance PrettyTPTP Char where
    prettyTPTP c
        | c == '-' = "_"
        | c == '.' = ""
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr (ord c - 8272)]
        | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
        | otherwise = show $ ord c

------------------------------------------------------------------------------
-- Pretty-printer for Agda types

instance PrettyTPTP NameId where
    prettyTPTP n = replace "@" "_" $ show n

instance PrettyTPTP QName where
    prettyTPTP (QName _ name) = prettyTPTP $ nameId name

------------------------------------------------------------------------------
-- Pretty-printer for FOL formulas

-- We use this instance because the names on the FOL formulas was
-- generated by a 'show qname'. Therefore, we need removed the
-- non-valid TPTP symbols. N.B. This instance require the flag
-- TypeSynonymInstances.
instance PrettyTPTP String where
    prettyTPTP s = concat $ map prettyTPTP s

instance PrettyTPTP TermFOL where
    prettyTPTP (FunFOL name [])    = changeToLower name
    prettyTPTP (FunFOL name terms) = changeToLower name ++
                                     "(" ++ prettyTPTP terms ++ ")"
    prettyTPTP (VarFOL name)       = changeToUpper name
    prettyTPTP (ConstFOL name)     = changeToLower name

instance PrettyTPTP [TermFOL] where
    prettyTPTP [] = []
    prettyTPTP (a : []) = prettyTPTP a
    prettyTPTP (a : as) = prettyTPTP a ++ "," ++ prettyTPTP as

instance PrettyTPTP FormulaFOL where
    -- We translate the hard-code FOL predicate kEqual as the
    -- predefined equality in the ATP.
    prettyTPTP (Predicate "kEqual" [t1, t2] ) =
       "( " ++ prettyTPTP t1 ++ " = " ++ prettyTPTP t2 ++ " )"

    prettyTPTP (Predicate "kEqual" _) = __IMPOSSIBLE__

    prettyTPTP (Predicate name terms) =
        changeToLower name ++ "(" ++ prettyTPTP terms ++ ")"

    prettyTPTP (And f1 f2) =
        "( " ++ prettyTPTP f1 ++ " & " ++ prettyTPTP f2 ++ " )"
    prettyTPTP (Or f1 f2) =
        "( " ++ prettyTPTP f1 ++ " | " ++ prettyTPTP f2 ++ " )"

    prettyTPTP (Not f) = '~' : prettyTPTP f

    prettyTPTP (Implies f1 f2) =
        "( " ++ prettyTPTP f1 ++ " => " ++ prettyTPTP f2 ++ " )"

    prettyTPTP (Equiv f1 f2) =
        "( " ++ prettyTPTP f1 ++ " <=> " ++ prettyTPTP f2 ++ " )"

    prettyTPTP (ForAll var f) =
        "( ! [" ++ changeToUpper var ++ "] : " ++
                    "( " ++ prettyTPTP (f (VarFOL var)) ++ " )" ++
        " )"

    prettyTPTP (Exists var f) =
        "( ! [" ++ changeToUpper var ++ "? : " ++
                    "( " ++ prettyTPTP (f (VarFOL var)) ++ " )" ++
        " )"

    prettyTPTP TRUE  = "$true "
    prettyTPTP FALSE = "$false "

------------------------------------------------------------------------------
-- Pretty-printer for annotated formulas

instance PrettyTPTP RoleATP where
    prettyTPTP AxiomATP      = "axiom"
    prettyTPTP ConjectureATP = "conjecture"
    prettyTPTP DefinitionATP = "axiom"
    prettyTPTP HintATP       = "axiom"

instance PrettyTPTP AnnotatedFormula where
    prettyTPTP (AF qName roleATP formula) =
        "fof(" ++
        prettyTPTP qName ++ ", " ++
        prettyTPTP roleATP ++ ", " ++
        prettyTPTP formula ++
        ")." ++ "\n\n"
