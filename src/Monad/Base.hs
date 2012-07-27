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
  ( askTOpt
  , getTDefs
  , getTVars
  , isTPragmaOption
  , isTVarsEmpty
  , modifyDefs
  , modifyPragmaOptions
  , newTVar
  , popTVar
  , pushTNewVar
  , pushTVar
  , runT
  , T
  , TState(..)  -- Required to avoid an Haddock warning.
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error  ( ErrorT(runErrorT) )
import Control.Monad.Reader ( MonadReader(ask), ReaderT(runReaderT) )

import Control.Monad.State
  ( evalState
  , evalStateT
  , modify
  , MonadState(get, put)
  , StateT
  )

import qualified Data.HashMap.Strict as HashMap ( empty )

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options     ( OptionsPragma )
import Agda.TypeChecking.Monad.Base ( Definitions )
import Agda.Utils.Impossible        ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import Options     ( Options, processOptions )
import Utils.IO    ( failureMsg )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------
-- | The translation monad state.

-- Note. Agda uses the type @[OptionsPragma]@ instead of the
-- @OptionPragma@ for the pragma options, but it doesn't seem
-- necessary in our case.
data TState =
  MkState { tDefs          ∷ Definitions    -- ^ Agda definitions.
          , tVars          ∷ [String]       -- ^ Variables names.
          , tPragmaOptions ∷ OptionsPragma  -- ^ Pragma options.
          }

-- The initial state.
initTState ∷ TState
initTState = MkState { tDefs          = HashMap.empty
                     , tVars          = []
                     , tPragmaOptions = []
                     }

-- | The environment.
env ∷ IO Options
env = do
  args ← getArgs
  case processOptions args of
    Left err → do failureMsg err
                  exitFailure
    Right o  → return o

-- | The translation monad.
type T = ErrorT String (StateT TState (ReaderT Options IO))

-- | Running the translation monad.
runT ∷ T a → IO (Either String a)
runT ta = env >>= runReaderT (evalStateT (runErrorT ta) initTState)

-- | Return 'True' if the list of variables in the translation monad
-- state is empty.
isTVarsEmpty ∷ T Bool
isTVarsEmpty = fmap (null . tVars) get

-- | @isTPragmaOption p@ returns 'True' if the pragma option @p@ is
-- set.
isTPragmaOption ∷ String → T Bool
isTPragmaOption p = do
  state ← get
  return (p `elem` tPragmaOptions state)

-- | Fresh variable.
newTVar ∷ T String
newTVar = fmap (evalState freshName . tVars) get

-- | Pop a variable from the translation monad state.
popTVar ∷ T ()
popTVar = do
  state ← get
  case tVars state of
    []       → __IMPOSSIBLE__
    (_ : xs) → put state { tVars = xs }

-- | Push a variable in the translation monad state.
pushTVar ∷ String → T ()
pushTVar x = do
  state ← get
  put state { tVars = x : tVars state }

-- | Create a fresh variable and push it in the translation monad state.
pushTNewVar ∷ T String
pushTNewVar = newTVar >>= \freshVar → pushTVar freshVar >> return freshVar

-- | Get the Agda 'Definitions' from the translation monad state.
getTDefs ∷ T Definitions
getTDefs = fmap tDefs get

-- | Ask for a concrete 'Options' from the translation monad
-- environment.
askTOpt ∷ (Options → a) → T a
askTOpt opt = fmap opt ask

-- | Get the variables from the translation monad state.
getTVars ∷ T [String]
getTVars = fmap tVars get

-- | Modify the Agda 'Definitions' in the translation monad state.
modifyDefs ∷ Definitions → T ()
modifyDefs defs = modify $ \s → s { tDefs = defs }

-- | Modify the 'OptionsPragma' in the translation monad state.
modifyPragmaOptions ∷ OptionsPragma → T ()
modifyPragmaOptions ps = modify $ \s → s { tPragmaOptions = ps }
