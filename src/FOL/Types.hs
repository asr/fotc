------------------------------------------------------------------------------
-- FOL types
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}

module FOL.Types where

------------------------------------------------------------------------------
-- FOL formulas.
-- Adapted from AgdaLight (Plugins.FOL.Types).
data TermFOL = FunFOL   String [TermFOL]
             | VarFOL   String
             | ConstFOL String -- AgdaLight hasn't them.
               deriving ( Show )

data FormulaFOL = TRUE
                | FALSE
                | Predicate String     [TermFOL]
                | Not       FormulaFOL
                | And       FormulaFOL FormulaFOL
                | Or        FormulaFOL FormulaFOL
                | Implies   FormulaFOL FormulaFOL
                | Equiv     FormulaFOL FormulaFOL
                | ForAll    String     (TermFOL -> FormulaFOL)
                | Exists    String     (TermFOL -> FormulaFOL)


instance Show FormulaFOL where
    show TRUE                = " TRUE "
    show FALSE               = " FALSE "
    show (Predicate name ts) = " Predicate " ++ show name ++ " " ++ show ts
    show (Not f)             = " Not " ++ show f
    show (And f1 f2)         = " And " ++ show f1 ++ show f2
    show (Or f1 f2)          = " Or " ++ show f1 ++ show f2
    show (Implies f1 f2)     = " Implies " ++ show f1 ++ show f2
    show (Equiv f1 f2)       = " Equiv " ++ show f1 ++ show f2
    show (ForAll var f)      = " ForAll " ++ show var ++ show (f $ VarFOL var)
    show (Exists var f)      = " Exists " ++ show var ++ show (f $ VarFOL var)
