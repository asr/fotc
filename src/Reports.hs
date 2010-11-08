-----------------------------------------------------------------------------
-- Reports via the verbose option
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Reports where

-- Haskell imports
import Control.Monad ( when )
import Control.Monad.Reader ( ask )
import Control.Monad.Trans ( liftIO )

-- Agda library imports
import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.Impossible ( Impossible (Impossible), throwImpossible )
-- import qualified Agda.Utils.IO.Locale as LocIO
-- import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie ( lookupPath )
import Agda.Utils.List ( wordsBy )

-- Local imports
import Common ( T )
import Options ( Options(optVerbose) )

#include "undefined.h"

-----------------------------------------------------------------------------
-- Nice way to report things via the verbose option.
-- Adapted from Agda.TypeChecking.Monad.Options.

getVerbosity :: T Verbosity
getVerbosity = do
  (_, opts) ← ask
  return $ optVerbose opts

type VerboseKey = String

-- | Precondition: The level must be non-negative.
verboseS :: VerboseKey → Int → T () → T ()
verboseS k n action | n < 0     =  __IMPOSSIBLE__
                    | otherwise = do
    t ← getVerbosity
    let ks = wordsBy (`elem` ".:") k
        m  = maximum $ 0 : Trie.lookupPath ks t
    when (n <= m) action

reportS :: VerboseKey → Int → String → T ()
reportS k n s = verboseS k n $ liftIO $ putStr (s ++ "\n")

reportSLn :: VerboseKey → Int → String → T ()
reportSLn k n s = verboseS k n $ liftIO $ putStrLn (s ++ "\n")
