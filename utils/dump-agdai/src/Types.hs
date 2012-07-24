{-# LANGUAGE UnicodeSyntax #-}

module Types ( printTypes ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Function ( on )

import qualified Data.HashMap.Strict as HashMap ( toList )

import Data.Int  ( Int32 )
import Data.List ( sortBy )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( Name(nameBindingSite)
  , QName(qnameName)
  )

import Agda.Syntax.Internal ( Type )

import Agda.TypeChecking.Monad.Base
  ( Definition
  , Definitions
  , defType
  , Interface(iSignature)
  , Signature(sigDefinitions)
  )

import Agda.Syntax.Position
  ( Interval(iStart)
  , Position(posLine)
  , rangeToInterval
  )

------------------------------------------------------------------------------
-- Auxiliary functions

qNameLine ∷ QName → Int32
qNameLine qName =
  case rangeToInterval $ nameBindingSite $ qnameName qName of
    Nothing → error "qNameLine"
    Just i  → posLine $ iStart i

-- We sort the @QName@'s by its position in the Agda module.
myQNameSort ∷ QName → QName → Ordering
myQNameSort = compare `on` qNameLine

myQNameDefinitionSort ∷ (QName, Definition) → (QName, Definition) → Ordering
myQNameDefinitionSort = myQNameSort `on` fst

------------------------------------------------------------------------------

printQNameType ∷ (QName, Definition) → IO ()
printQNameType (qName, def) = do

  let ty ∷ Type
      ty = defType def

  putStrLn $ "Qname: " ++ show qName
  putStrLn $ "Type: "  ++ show ty ++ "\n"

printTypes ∷ Interface → IO ()
printTypes i = do

  putStrLn "\nTypes ***********************************************************"

  let defs ∷ Definitions
      defs = sigDefinitions $ iSignature i

  mapM_ printQNameType $ sortBy myQNameDefinitionSort $ HashMap.toList defs
