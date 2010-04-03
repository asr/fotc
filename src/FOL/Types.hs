------------------------------------------------------------------------------
-- FOL types
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}

module FOL.Types where

{-| FOL formulas -}
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
    show (ForAll var f)        = " ForAll " ++ var ++ show (f $ VarFOL var)
    show (Exists var f)        = " Exists " ++ var ++ show (f $ VarFOL var)
    show TRUE                  = " TRUE "
    show FALSE                 = " FALSE "
