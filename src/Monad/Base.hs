------------------------------------------------------------------------------
-- |
-- Module      : Monad.Base
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
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
  ( AllDefinitions
  , getTAllDefs
  , getTOpts
  , getTVars
  , isTVarsEmpty
  , newTVar
  , popTVar
  , pushTVar
  , runT
  , T
  , TState(tAllDefs, tOpts, tVars)
  ) where

-- Haskell imports
import Control.Monad.Error ( ErrorT, runErrorT )
import Control.Monad.State
  ( evalState
  , evalStateT
  , get
  , modify
  , MonadState
  , StateT
  )

import qualified Data.Map as Map ( empty )

-- Agda library imports
import Agda.TypeChecking.Monad.Base ( Definitions )
import Agda.Utils.Impossible        ( Impossible(Impossible), throwImpossible )

-- Local imports
import Options     ( defaultOptions, Options )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------

type AllDefinitions = Definitions

data TState = MkState { tAllDefs ∷ AllDefinitions
                      , tOpts    ∷ Options
                      , tVars    ∷ [String]
                      }

-- The initial state.
initTState ∷ TState
initTState = MkState { tAllDefs = Map.empty
                     , tOpts    = defaultOptions
                     , tVars    = []
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
  modify $ \s → s { tVars = x : tVars state }

popTVar ∷ T ()
popTVar = do
  state ← get
  case tVars state of
    []       → __IMPOSSIBLE__
    (_ : xs) → modify $ \s → s { tVars = xs }

newTVar ∷ T String
newTVar = fmap (evalState freshName . tVars) get

getTAllDefs ∷ T AllDefinitions
getTAllDefs = fmap tAllDefs get

getTOpts ∷ T Options
getTOpts = fmap tOpts get

getTVars ∷ T [String]
getTVars = fmap tVars get
