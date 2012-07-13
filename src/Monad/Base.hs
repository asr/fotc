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
  , getTOpt
  , getTVars
  , isTPragmaOption
  , isTVarsEmpty
  , modifyDefs
  , modifyOpts
  , modifyPragmaOptions
  , newTVar
  , popTVar
  , pushTVar
  , runT
  , T
  , TState(..)  -- Required to avoid an Haddock warning.
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( ErrorT(runErrorT) )

import Control.Monad.State
  ( evalState
  , evalStateT
  , modify
  , MonadState(get, put)
  , StateT
  )

import qualified Data.HashMap.Strict as HashMap ( empty )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options     ( OptionsPragma )
import Agda.TypeChecking.Monad.Base ( Definitions )
import Agda.Utils.Impossible        ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import Options     ( defaultOptions, Options )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------
-- | The translation monad state.

-- Note. Agda uses the type @[OptionsPragma]@ instead of the
-- @OptionPragma@ for the pragma options, but it doesn't seem
-- necessary in our case.
data TState =
  MkState { tDefs          ∷ Definitions    -- ^ Agda definitions.
          , tOpts          ∷ Options        -- ^ Command-line options.
          , tVars          ∷ [String]       -- ^ Variables names.
          , tPragmaOptions ∷ OptionsPragma  -- ^ Pragma options.
          }

-- The initial state.
initTState ∷ TState
initTState = MkState { tDefs          = HashMap.empty
                     , tOpts          = defaultOptions
                     , tVars          = []
                     , tPragmaOptions = []
                     }

-- | The translation monad.
type T = ErrorT String (StateT TState IO)

-- | Running the translation monad.
runT ∷ T a → IO (Either String a)
runT ta = evalStateT (runErrorT ta) initTState

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

-- | Push a variable in the translation monad state.
pushTVar ∷ String → T ()
pushTVar x = do
  state ← get
  put state { tVars = x : tVars state }

-- | Pop a variable from the translation monad state.
popTVar ∷ T ()
popTVar = do
  state ← get
  case tVars state of
    []       → __IMPOSSIBLE__
    (_ : xs) → put state { tVars = xs }

-- | Add a new variable to the translation monad state.
newTVar ∷ T String
newTVar = fmap (evalState freshName . tVars) get

-- | Get the Agda 'Definitions' from the translation monad state.
getTDefs ∷ T Definitions
getTDefs = fmap tDefs get

-- | Get a concrete 'Options' from the translation monad state.
getTOpt ∷ (Options → a) → T a
getTOpt opt = fmap (opt . tOpts) get

-- | Get the variables from the translation monad state.
getTVars ∷ T [String]
getTVars = fmap tVars get

-- | Modify the Agda 'Definitions' in the translation monad state.
modifyDefs ∷ Definitions → T ()
modifyDefs defs = modify $ \s → s { tDefs = defs }

-- | Modify the 'Options' in the translation monad state.
modifyOpts ∷ Options → T ()
modifyOpts opts = modify $ \s → s { tOpts = opts }

-- | Modify the 'OptionsPragma' in the translation monad state.
modifyPragmaOptions ∷ OptionsPragma → T ()
modifyPragmaOptions ps = modify $ \s → s { tPragmaOptions = ps }
