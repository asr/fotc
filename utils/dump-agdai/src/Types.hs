{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fno-warn-auto-orphans #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Types ( printQNames, printTypes ) where

------------------------------------------------------------------------------
-- Haskell imports

import qualified Data.HashMap.Strict as HashMap ( keys, toList )

import Data.Int  ( Int32 )
import Data.List ( sort )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( Name(nameBindingSite)
  , QName(qnameName)
  )

import Agda.Syntax.Internal ( Type )

import Agda.TypeChecking.Monad.Base
  ( Definition(defName)
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

qNameLine ∷ QName → Int32
qNameLine qName =
  case rangeToInterval $ nameBindingSite $ qnameName qName of
    Nothing → error "qNameLine"
    Just i  → posLine $ iStart i

-- Orphan instance.
instance Eq Definition where
  def1 == def2 = defName def1 == defName def2

-- Orphan instance.
instance Ord Definition where
  def1 `compare` def2 = defName def1 `compare` defName def2

instance Ord QName where
  qName1 `compare` qName2 = qNameLine qName1 `compare` qNameLine qName1

printQNameType ∷ (QName, Definition) → IO ()
printQNameType (qname, def) = do

  let ty ∷ Type
      ty = defType def

  putStrLn $ "Qname: " ++ show qname
  putStrLn $ "Type: "  ++ show ty ++ "\n"

printTypes ∷ Interface → IO ()
printTypes i = do

  putStrLn "\nTypes ***********************************************************"

  let defs ∷ Definitions
      defs = sigDefinitions $ iSignature i

  mapM_ printQNameType $ sort $ HashMap.toList defs

printQNames ∷ Interface → IO ()
printQNames i = do
  let defs ∷ Definitions
      defs = sigDefinitions $ iSignature i

  putStrLn "\nQNames ***********************************************************"
  print $ sort $ HashMap.keys defs
