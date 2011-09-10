{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

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
import Control.Monad.Error ( ErrorT, MonadError, runErrorT )
import Control.Monad.State
  ( evalState
  , evalStateT
  , get
  , modify
  , MonadState
  , StateT
  )
import Control.Monad.Trans ( MonadIO )

import qualified Data.Map as Map ( empty )

-- Agda library imports
import Agda.TypeChecking.Monad.Base ( Definitions )

-- Local imports
import Options     ( defaultOptions, Options )
import Utils.Names ( freshName )

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

-- Adapted from: Real World Haskell (Chapter 18. Monad transformers)
-- | The translation monad.
newtype T a = MkT { runA ∷ ErrorT String (StateT TState IO) a }
  -- Requires GeneralizedNewtypeDeriving
  deriving ( Functor
           , Monad
           , MonadIO
           , MonadError String
           , MonadState TState
           )

runT ∷ T a → IO (Either String a)
runT ta = evalStateT (runErrorT (runA ta)) initTState

isTVarsEmpty ∷ T Bool
isTVarsEmpty = fmap (null . tVars) get

pushTVar ∷ String → T ()
pushTVar x = do
  state ← get
  let xs ∷ [String]
      xs = tVars state
  modify $ \s → s { tVars = x : xs }

popTVar ∷ T ()
popTVar = do
  state ← get
  let xs ∷ [String]
      xs = tVars state
  modify $ \s → s { tVars = tail xs }

newTVar ∷ T String
newTVar = fmap (evalState freshName . tVars) get

getTAllDefs ∷ T AllDefinitions
getTAllDefs = fmap tAllDefs get

getTOpts ∷ T Options
getTOpts = fmap tOpts get

getTVars ∷ T [String]
getTVars = fmap tVars get
