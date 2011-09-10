{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- |
-- Module      : FOL.Types
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- FOL types.
------------------------------------------------------------------------------

module FOL.Types ( FOLFormula(..), FOLTerm(..) ) where

------------------------------------------------------------------------------
-- Adapted from AgdaLight (Plugins.FOL.Types).

-- FOL terms.
data FOLTerm = FOLFun String [FOLTerm]
             | FOLVar String
               deriving Show

-- | FOL formulas.
data FOLFormula = TRUE
                | FALSE
                | Predicate String     [FOLTerm]
                | Not       FOLFormula
                | And       FOLFormula FOLFormula
                | Or        FOLFormula FOLFormula
                | Implies   FOLFormula FOLFormula
                | Equiv     FOLFormula FOLFormula
                | ForAll    String     (FOLTerm → FOLFormula)
                | Exists    String     (FOLTerm → FOLFormula)

instance Show FOLFormula where
  show TRUE                = " TRUE "
  show FALSE               = " FALSE "
  show (Predicate name ts) = " Predicate " ++ show name ++ " " ++ show ts
  show (Not f)             = " Not " ++ show f
  show (And f1 f2)         = " And " ++ show f1 ++ show f2
  show (Or f1 f2)          = " Or " ++ show f1 ++ show f2
  show (Implies f1 f2)     = " Implies " ++ show f1 ++ show f2
  show (Equiv f1 f2)       = " Equiv " ++ show f1 ++ show f2
  show (ForAll var f)      = " ForAll " ++ show var ++ show (f $ FOLVar var)
  show (Exists var f)      = " Exists " ++ show var ++ show (f $ FOLVar var)
