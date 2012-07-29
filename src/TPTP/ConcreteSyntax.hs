------------------------------------------------------------------------------
-- |
-- Module      : TPTP.ConcreteSyntax
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- TPTP concrete syntax.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.ConcreteSyntax
  ( ToTPTP(toTPTP)
  , TPTP  -- Required to avoid an Haddock warning.
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Char
  ( chr
  , isAsciiLower
  , isAsciiUpper
  , isDigit
  , isUpper
  , ord
  , toUpper
  )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( Name(nameId), QName(QName) )

import Agda.Syntax.Common
  ( NameId(NameId)
  , ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint)
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types
  ( FOLFormula(And
              , Equiv
              , Exists
              , FALSE
              , ForAll
              , Implies
              , Not
              , Or
              , Predicate
              , TRUE
              )
  , FOLTerm(FOLFun, FOLVar)
  )

import TPTP.Types ( AF(AF) )

#include "../undefined.h"

------------------------------------------------------------------------------

-- | TPTP type synonymous.
type TPTP = String

-- | Translation to TPTP concrete syntax.
class ToTPTP a where
  toTPTP ∷ a → TPTP

------------------------------------------------------------------------------
-- Auxiliary functions

-- We prefixed the names with @n@ because TPTP does not accept names
-- starting with digits or @_@.
prefixLetter ∷ TPTP → TPTP
prefixLetter []           = __IMPOSSIBLE__
prefixLetter name@(x : _)
  | isDigit x || x == '_'  = 'n' : name
  | otherwise              = name

toUpperFirstSymbol ∷ TPTP → TPTP
toUpperFirstSymbol []       = __IMPOSSIBLE__
toUpperFirstSymbol (x : xs) =  toUpper x : xs

-- From the technical manual of TPTP
-- (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml)

-- ... variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

-- If a function name start by an uppper case letter, we add a @'f'@.
functionName2TPTP ∷ String → TPTP
functionName2TPTP name =
  if isUpper (head nameTPTP) then 'f' : nameTPTP else nameTPTP
  where
  nameTPTP ∷ String
  nameTPTP = toTPTP name

-- If a predicate name start by an uppper case letter, we add a @'p'@.
predicateName2TPTP ∷ String → TPTP
predicateName2TPTP name =
  if isUpper (head nameTPTP) then 'p' : nameTPTP else nameTPTP
  where
  nameTPTP ∷ String
  nameTPTP = toTPTP name

-- If a variable name start by an lower case letter, we add a @'V'@.
--
-- We are not using this function because we don't have a test case
-- where the variables names clash.

-- varName2TPTP ∷ String → TPTP
-- varName2TPTP name =
--   if isLower (head nameTPTP) then 'V' : nameTPTP else nameTPTP
--   where
--   nameTPTP ∷ String
--   nameTPTP = toTPTP name

------------------------------------------------------------------------------
-- Translation of Agda/Haskell types to TPTP concrete syntax.

instance ToTPTP Char where
  toTPTP c
    -- From Agda wiki: A name part is a string of printable characters
    -- not containing any of the following characters: _;.’”(){}@.
    | c == ';'  = __IMPOSSIBLE__
    | c == '\'' = __IMPOSSIBLE__
    | c == '"'  = __IMPOSSIBLE__
    | c == '('  = __IMPOSSIBLE__
    | c == ')'  = __IMPOSSIBLE__
    | c == '{'  = __IMPOSSIBLE__
    | c == '}'  = __IMPOSSIBLE__
    | c == '@'  = __IMPOSSIBLE__
    -- We use the character @_@ to separate the Agda NameId (see
    -- below).
    | c == '_' = [c]
    -- The character is a subscript number (i.e. ₀, ₁, ...).
    | ord c `elem` [8320 .. 8329]                   = [chr (ord c - 8272)]
    | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
    | otherwise                                     = show $ ord c

------------------------------------------------------------------------------
-- Translation of Agda types to TPTP concrete syntax.

instance ToTPTP NameId where
  -- The @Show@ instance @Agda.Syntax.Abstract.Name@ separates the
  -- unique identifier of the top-level module (the second argument)
  -- with '@'. We use '_' because '@' is not TPTP valid.
  toTPTP  (NameId x i)  = prefixLetter $ show x ++ "_" ++ show i

instance ToTPTP QName where
  toTPTP (QName _ name) = toTPTP $ nameId name

------------------------------------------------------------------------------
-- Translation of first-order logic formulae to TPTP concrete syntax.

-- We use this instance because the names on the first-order logic
-- formulae was generated by a @show qname@. Therefore, we need drop
-- the non-valid TPTP symbols.

-- Requires @TypeSynonymInstances@.
instance ToTPTP String where
  toTPTP = prefixLetter . concatMap toTPTP

instance ToTPTP FOLTerm where
  toTPTP (FOLFun name [])    = functionName2TPTP name
  toTPTP (FOLFun name terms) = functionName2TPTP name
                               ++ "(" ++ toTPTP terms ++ ")"
  toTPTP (FOLVar name)       = toUpperFirstSymbol name

-- Requires @FlexibleInstances@.
instance ToTPTP [FOLTerm] where
  toTPTP []       = __IMPOSSIBLE__
  toTPTP (a : []) = toTPTP a
  toTPTP (a : as) = toTPTP a ++ "," ++ toTPTP as

instance ToTPTP FOLFormula where
  -- We translate the hard-coded first-order logic predicate @kEqual@
  -- as the predefined equality in the ATP.
  toTPTP (Predicate "kEqual" [t1, t2] ) =
    "( " ++ toTPTP t1 ++ " = " ++ toTPTP t2 ++ " )"

  toTPTP (Predicate "kEqual" _) = __IMPOSSIBLE__

  -- If the predicate represents a propositional logic variable,
  -- following the TPTP syntax, we do not print the internal
  -- parenthesis.
  toTPTP (Predicate name []) = "( " ++ predicateName2TPTP name ++ " )"

  toTPTP (Predicate name terms) =
    "( " ++ predicateName2TPTP name ++ "(" ++ toTPTP terms ++ ")" ++ " )"

  toTPTP (And f1 f2)     = "( " ++ toTPTP f1 ++ " & " ++ toTPTP f2 ++ " )"
  toTPTP (Or f1 f2)      = "( " ++ toTPTP f1 ++ " | " ++ toTPTP f2 ++ " )"
  toTPTP (Not f)         = "( " ++ '~' : toTPTP f ++ " )"
  toTPTP (Implies f1 f2) = "( " ++ toTPTP f1 ++ " => " ++ toTPTP f2 ++ " )"
  toTPTP (Equiv f1 f2)   = "( " ++ toTPTP f1 ++ " <=> " ++ toTPTP f2 ++ " )"

  toTPTP (ForAll var f) =
    "( ! [" ++ toUpperFirstSymbol var ++ "] : "
    ++ toTPTP (f (FOLVar var))
    ++ " )"

  toTPTP (Exists var f) =
    "( ? [" ++ toUpperFirstSymbol var ++ "] : "
    ++ toTPTP (f (FOLVar var))
    ++ " )"

  toTPTP TRUE  = "( " ++ "$true" ++ " )"
  toTPTP FALSE = "( " ++ "$false" ++ " )"

------------------------------------------------------------------------------
-- Translation of annotated formulae to TPTP concrete syntax.

instance ToTPTP ATPRole where
  toTPTP ATPAxiom      = "axiom"
  toTPTP ATPConjecture = "conjecture"
  toTPTP ATPDefinition = "definition"
  toTPTP ATPHint       = "hypothesis"

instance ToTPTP AF where
  toTPTP (AF qName atpRole formula) =
    "fof("
    ++ toTPTP qName ++ ", "
    ++ toTPTP atpRole ++ ", "
    ++ toTPTP formula
    ++ ")." ++ "\n\n"
