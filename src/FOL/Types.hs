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

data FOLTerm = FOLFun String [FOLTerm]
             | FOLVar String
             | FOLConst String -- AgdaLight hasn't them.
               deriving ( Show )

data Formula = Predicate String [FOLTerm]
             | And Formula Formula
             | Or Formula Formula
             | Not Formula
             | Implies Formula Formula
             | Equiv Formula Formula
             | ForAll String (FOLTerm -> Formula)
             | Exists String (FOLTerm -> Formula)
             | TRUE
             | FALSE

instance Show Formula where
    show (Predicate name terms) = " Predicate " ++ name ++ " " ++ show terms
    show (And f1 f2)           = " And " ++ show f1 ++ show f2
    show (Or f1 f2)            = " Or " ++ show f1 ++ show f2
    show (Not f)               = " Not " ++ show f
    show (Implies f1 f2)       = " Implies " ++ show f1 ++ show f2
    show (Equiv f1 f2)         = " Equiv " ++ show f1 ++ show f2
    show (ForAll var f)        = " ForAll " ++ var ++ (show $ f (FOLVar var))
    show (Exists var f)        = " Exists " ++ var ++ (show $ f (FOLVar var))
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
                    "( " ++ (showTPTP $ f (FOLVar var)) ++ " )" ++
        " )"

    showTPTP (Exists var f) =
        "( ! [" ++ (map toUpper var) ++ "?: " ++
                    "( " ++ (showTPTP $ f (FOLVar var)) ++ " )" ++
        " )"

    showTPTP TRUE  = "$true "
    showTPTP FALSE = "$false "

instance ShowTPTP FOLTerm where
    showTPTP (FOLFun name [])    = name
    showTPTP (FOLFun name terms) = name ++ "(" ++ showTPTP terms ++ ")"
    showTPTP (FOLVar name)       = map toUpper name
    showTPTP (FOLConst name)     = map toLower name

instance (ShowTPTP a) => ShowTPTP [a] where
    showTPTP [] = []
    showTPTP (a : []) = showTPTP a
    showTPTP (a : as) = showTPTP a ++ "," ++ showTPTP as