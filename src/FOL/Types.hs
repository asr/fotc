{-# LANGUAGE StandaloneDeriving
           , FlexibleInstances
 #-}

-- Adapted from AgdaLight (Plugins.FOL.Types).

module FOL.Types where

{-| FOL propositions -}
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
    show (Predicate str terms) = " Predicate " ++ str ++ " " ++ show terms
    show (And f1 f2)           = " And " ++ show f1 ++ show f2
    show (Or f1 f2)            = " Or " ++ show f1 ++ show f2
    show (Not f)               = " Not " ++ show f
    show (Implies f1 f2)       = " Implies " ++ show f1 ++ show f2
    show (Equiv f1 f2)         = " Equiv " ++ show f1 ++ show f2
    show (ForAll var f)        = " ForAll " ++ var ++ (show $ f (FOLVar var))
    show (Exists var f)        = " Exists " ++ var ++ (show $ f (FOLVar var))
    show TRUE                  = " TRUE "
    show FALSE                 = " FALSE "
