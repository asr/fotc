------------------------------------------------------------------------------
-- Common entities
------------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module Common
    ( AllDefinitions
    , fakeFile
    , initTState
    , runT
    , T
    , TEnv
    , TopLevelDefinitions
    , TState
    )
    where

-- Haskell imports
import Control.Monad.Error  ( ErrorT, MonadError, runErrorT )
import Control.Monad.Reader ( MonadReader, ReaderT, runReaderT )
import Control.Monad.State  ( evalStateT, MonadState, StateT )
import Control.Monad.Trans  ( MonadIO )

import qualified Data.Map as Map ( empty )

-- Agda library imports
import Agda.TypeChecking.Monad.Base ( Definitions )

-- Local imports
import Options ( defaultOptions, Options )

------------------------------------------------------------------------------
-- Common types

type AllDefinitions      = Definitions
type TopLevelDefinitions = Definitions

------------------------------------------------------------------------------
-- The translation monad

-- The type TState represents the names of variables bounded in the Agda
-- types.
type TState = [String]

-- The initial state.
initTState :: TState
initTState = []

-- The environment.
type TEnv = (AllDefinitions, Options, FilePath)

fakeFile :: FilePath
fakeFile = ""

-- The initial environment.
initTEnv :: TEnv
initTEnv = (Map.empty, defaultOptions, fakeFile)

-- The translation monad.
-- Adapted from: Real World Haskell (Chapter 18. Monad transformers)
newtype T a = MkT { runA :: ErrorT String (StateT TState (ReaderT TEnv IO)) a }
        -- Requires GeneralizedNewtypeDeriving
        deriving ( Functor
                 , Monad
                 , MonadIO
                 , MonadError String
                 , MonadState TState
                 , MonadReader TEnv
                 )

runT :: T a → IO (Either String a)
runT ta = runReaderT (evalStateT (runErrorT (runA ta)) initTState) initTEnv
