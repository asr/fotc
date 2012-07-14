{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

-- Haskell imports
import System.Environment ( getArgs )
import System.Exit        ( exitFailure)

-- Agda library imports
import Agda.Utils.Impossible ( catchImpossible )

-- Local imports
import ReadInterface ( myReadInterface )
import Types         ( printTypes )

------------------------------------------------------------------------------

main ∷ IO ()
main = do
  file ← fmap head getArgs
  i    ← myReadInterface file

  catchImpossible (print i) $
    \e → do putStr $ show e
            exitFailure

  catchImpossible (printTypes i) $
    \e → do putStr $ show e
            exitFailure
