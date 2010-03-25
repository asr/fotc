------------------------------------------------------------------------------
-- Translation from FOL formulas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.FOL2TPTP where

-- Haskell imports
import Data.Char

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

-- Local imports
import FOL.Types

#include "../undefined.h"

------------------------------------------------------------------------------

-- ToDo: It is necessary generalize this function.
nameTPTP :: String -> String
nameTPTP "+"   = "add"
nameTPTP "-"   = "minus"
nameTPTP "_>_" = "gt"
nameTPTP "_≤_" = "le"
nameTPTP name  = map toLower name

class ShowTPTP a where
    showTPTP :: a -> String

instance (ShowTPTP a) => ShowTPTP [a] where
    showTPTP [] = []
    showTPTP (a : []) = showTPTP a
    showTPTP (a : as) = showTPTP a ++ "," ++ showTPTP as

instance ShowTPTP Formula where
    -- We translate the hard-code FOL predicate kEqual as the
    -- predefined equality in the ATP.
    showTPTP (Predicate "kEqual" [t1, t2] ) =
       "( " ++ showTPTP t1 ++ " = " ++ showTPTP t2 ++ " )"

    showTPTP (Predicate "kEqual" _) = __IMPOSSIBLE__

    showTPTP (Predicate name terms) =
        nameTPTP name ++ "(" ++ showTPTP terms ++ ")"

    showTPTP (And f1 f2) =
        "( " ++ showTPTP f1 ++ " & " ++ showTPTP f2 ++ " )"
    showTPTP (Or f1 f2) =
        "( " ++ showTPTP f1 ++ " | " ++ showTPTP f2 ++ " )"

    showTPTP (Not f) = "~" ++ showTPTP f

    showTPTP (Implies f1 f2) =
        "( " ++ showTPTP f1 ++ " => " ++ showTPTP f2 ++ " )"

    showTPTP (Equiv f1 f2) =
        "( " ++ showTPTP f1 ++ " <=> " ++ showTPTP f2 ++ " )"

    showTPTP (ForAll var f) =
        "( ! [" ++ (map toUpper var) ++ "] : " ++
                    "( " ++ (showTPTP $ f (VarFOL var)) ++ " )" ++
        " )"

    showTPTP (Exists var f) =
        "( ! [" ++ (map toUpper var) ++ "? : " ++
                    "( " ++ (showTPTP $ f (VarFOL var)) ++ " )" ++
        " )"

    showTPTP TRUE  = "$true "
    showTPTP FALSE = "$false "

instance ShowTPTP TermFOL where
    showTPTP (FunFOL name [])    = nameTPTP name
    showTPTP (FunFOL name terms) = nameTPTP name ++ "(" ++ showTPTP terms ++ ")"
    showTPTP (VarFOL name)       = map toUpper name
    showTPTP (ConstFOL name)     = map toLower name
