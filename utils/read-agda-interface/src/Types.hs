{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Types ( printTypes ) where

------------------------------------------------------------------------------
-- Haskell imports

-- #if MIN_VERSION_Agda(2,2,11)
-- import qualified Data.Map as Map ( toList )
-- #else
import qualified Data.HashMap.Strict as HashMap ( toList )
-- #endif

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Internal ( Type )
import Agda.TypeChecking.Monad.Base
  ( Definition
  , Definitions
  , defType
  , Interface(iSignature)
  , Signature(sigDefinitions)
  )

------------------------------------------------------------------------------

printQNameType ∷ (QName, Definition) → IO ()
printQNameType (qName, def) = do

  let ty ∷ Type
      ty = defType def

  putStrLn $ "Qname: " ++ show qName
  putStrLn $ "Type: "  ++ show ty ++ "\n"

printTypes ∷ Interface → IO ()
printTypes i = do

  let defs ∷ Definitions
      defs = sigDefinitions $ iSignature i

-- #if MIN_VERSION_Agda(2,2,11)
--  mapM_ printQNameType (Map.toList defs)
-- #else
  mapM_ printQNameType (HashMap.toList defs)
-- #endif
