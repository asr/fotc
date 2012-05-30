{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

-- TODO: 29 May 2012. Haddock 2.10.0 requires the LANGUAGE pragmas
-- before the module description.

------------------------------------------------------------------------------
-- |
-- Module      : Monad.Base
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- The translation monad.
------------------------------------------------------------------------------

module Monad.Base
  ( getTDefs
  , getTOpts
  , getTVars
  , isTVarsEmpty
  , modifyDefs
  , modifyOpts
  , newTVar
  , popTVar
  , pushTVar
  , runT
  , T
  , TState(..)  -- Required to avoid an Haddock warning.
  ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>=), fail) )
#endif

import Control.Monad.Error ( ErrorT(runErrorT) )

import Control.Monad.State
  ( evalState
  , evalStateT
  , modify
  , MonadState(get, put)
  , StateT
  )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Bool     ( Bool )
import Data.Either   ( Either )
import Data.Function ( ($), (.) )
import Data.Functor  ( fmap )

import qualified Data.HashMap.Strict as HashMap ( empty )

import Data.List     ( null )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif

import System.IO ( IO )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.TypeChecking.Monad.Base ( Definitions )
import Agda.Utils.Impossible        ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import Options     ( defaultOptions, Options )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------
-- | The translation monad state.
data TState = MkState { tDefs ∷ Definitions -- ^ Agda definitions.
                      , tOpts ∷ Options     -- ^ Command-line options.
                      , tVars ∷ [String]    -- ^ Variables names.
                      }

-- The initial state.
initTState ∷ TState
initTState = MkState { tDefs = HashMap.empty
                     , tOpts = defaultOptions
                     , tVars = []
                     }

-- | The translation monad.
type T = ErrorT String (StateT TState IO)

runT ∷ T a → IO (Either String a)
runT ta = evalStateT (runErrorT ta) initTState

isTVarsEmpty ∷ T Bool
isTVarsEmpty = fmap (null . tVars) get

pushTVar ∷ String → T ()
pushTVar x = do
  state ← get
  put state { tVars = x : tVars state }

popTVar ∷ T ()
popTVar = do
  state ← get
  case tVars state of
    []       → __IMPOSSIBLE__
    (_ : xs) → put state { tVars = xs }

newTVar ∷ T String
newTVar = fmap (evalState freshName . tVars) get

getTDefs ∷ T Definitions
getTDefs = fmap tDefs get

getTOpts ∷ T Options
getTOpts = fmap tOpts get

getTVars ∷ T [String]
getTVars = fmap tVars get

modifyDefs ∷ Definitions → T ()
modifyDefs defs = modify $ \s → s { tDefs = defs }

modifyOpts ∷ Options → T ()
modifyOpts opts = modify $ \s → s { tOpts = opts }
