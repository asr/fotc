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

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Base
  ( getTDefs
  , getTOpts
  , getTVars
  , isTVarsEmpty
  , newTVar
  , popTVar
  , pushTVar
  , runT
  , T
  , TState(tDefs, tOpts)
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( ErrorT(runErrorT) )

import Control.Monad.State
  ( evalState
  , evalStateT
  , MonadState(get, put)
  , StateT
  )

import qualified Data.Map as Map ( empty )

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
initTState = MkState { tDefs = Map.empty
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
