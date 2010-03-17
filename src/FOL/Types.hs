------------------------------------------------------------------------------
-- FOL types
------------------------------------------------------------------------------

{-# LANGUAGE StandaloneDeriving
           , FlexibleInstances
 #-}

module FOL.Types where

-- Haskell imports
import Data.Char

------------------------------------------------------------------------------

{-| FOL propositions -}
-- Adapted from AgdaLight (Plugins.FOL.Types).

data TermFOL = FunFOL String [TermFOL]
             | VarFOL String
             | ConstFOL String -- AgdaLight hasn't them.
               deriving ( Show )

data Formula = Predicate String [TermFOL]
                | And Formula Formula
                | Or Formula Formula
                | Not Formula
                | Implies Formula Formula
                | Equiv Formula Formula
                | ForAll String (TermFOL -> Formula)
                | Exists String (TermFOL -> Formula)
                | TRUE
                | FALSE

instance Show Formula where
    show (Predicate name terms) = " Predicate " ++ name ++ " " ++ show terms
    show (And f1 f2)           = " And " ++ show f1 ++ show f2
    show (Or f1 f2)            = " Or " ++ show f1 ++ show f2
    show (Not f)               = " Not " ++ show f
    show (Implies f1 f2)       = " Implies " ++ show f1 ++ show f2
    show (Equiv f1 f2)         = " Equiv " ++ show f1 ++ show f2
    show (ForAll var f)        = " ForAll " ++ var ++ (show $ f (VarFOL var))
    show (Exists var f)        = " Exists " ++ var ++ (show $ f (VarFOL var))
    show TRUE                  = " TRUE "
    show FALSE                 = " FALSE "

class ShowTPTP a where
    showTPTP :: a -> String

instance ShowTPTP Formula where
    showTPTP (Predicate name terms) =
        (map toLower name) ++ "(" ++ showTPTP terms ++ ")"

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
        "( ! [" ++ (map toUpper var) ++ "]: " ++
                    "( " ++ (showTPTP $ f (VarFOL var)) ++ " )" ++
        " )"

    showTPTP (Exists var f) =
        "( ! [" ++ (map toUpper var) ++ "?: " ++
                    "( " ++ (showTPTP $ f (VarFOL var)) ++ " )" ++
        " )"

    showTPTP TRUE  = "$true "
    showTPTP FALSE = "$false "

instance ShowTPTP TermFOL where
    showTPTP (FunFOL name [])    = name
    showTPTP (FunFOL name terms) = name ++ "(" ++ showTPTP terms ++ ")"
    showTPTP (VarFOL name)       = map toUpper name
    showTPTP (ConstFOL name)     = map toLower name

instance (ShowTPTP a) => ShowTPTP [a] where
    showTPTP [] = []
    showTPTP (a : []) = showTPTP a
    showTPTP (a : as) = showTPTP a ++ "," ++ showTPTP as