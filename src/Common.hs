------------------------------------------------------------------------------
-- Common entities
------------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module Common
    ( AllDefinitions
    , iVarNames
    , runT
    , T
    , TopLevelDefinitions
    , Vars
    )
    where

-- Haskell imports
import Control.Monad.Error ( ErrorT, MonadError, runErrorT )
import Control.Monad.Reader ( MonadReader, ReaderT, runReaderT )
import Control.Monad.State ( evalStateT, MonadState, StateT )
import Control.Monad.Trans ( MonadIO )

-- Agda library imports
import Agda.TypeChecking.Monad.Base ( Definitions )

-- Local imports
import Options ( Options )

------------------------------------------------------------------------------
-- Common types

type AllDefinitions      = Definitions
type TopLevelDefinitions = Definitions

------------------------------------------------------------------------------
-- The translation monad

-- The statet 'Vars' represents the names of variables bounded in the Agda
-- types.
type Vars = [String]

-- The initial state.
iVarNames :: Vars
iVarNames = []

-- The environment.
type Env = (AllDefinitions, Options)

-- The translation monad.
-- Adapted from: Real World Haskell (Chapter 18. Monad transformers)
newtype T a = MkT { runA :: ErrorT String (StateT Vars (ReaderT Env IO)) a }
        -- Requires GeneralizedNewtypeDeriving
        deriving ( Functor
                 , Monad
                 , MonadIO
                 , MonadError String
                 , MonadState Vars
                 , MonadReader Env
                 )

runT :: T a → Vars → Env → IO (Either String a)
runT ta vars env = runReaderT (evalStateT (runErrorT (runA ta)) vars) env
