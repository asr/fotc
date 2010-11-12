-----------------------------------------------------------------------------
-- Process the command line arguments
-----------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Options.Process ( processOptions ) where

-- Haskell imports
import Control.Monad.Error ( throwError )

import System.Console.GetOpt
    ( ArgOrder (Permute)
    , getOpt
    )

-- Local imports
import Common ( fakeFile, T )
import Options
    ( defaultOptions
    , defaultOptATP
    , options
    , Options(optATP, optHelp)
    )

-----------------------------------------------------------------------------
-- This function is not defined in the module Options.hs to avoid a
-- circularity.
processOptions :: [String] → T (Options, String)
processOptions argv =
  case getOpt Permute options argv of
    ([], [], []) → return (defaultOptions { optHelp = True } , fakeFile)

    (o, files, []) → do
      let opts :: Options
          opts = foldl (flip id) defaultOptions o

      let finalOpts :: Options
          finalOpts =
              if null (optATP opts)  -- No ATPs was chosen.
              then opts { optATP = defaultOptATP }  -- We set up the
                                                    -- defaults ATPs.
              else opts

      case files of
        []       → return (finalOpts, fakeFile)
        (x : []) → return (finalOpts, x)
        _        → throwError "Only one input file allowed"

    (_, _, errors) → throwError $ unlines errors
