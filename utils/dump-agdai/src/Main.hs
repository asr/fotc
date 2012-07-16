{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

-- Haskell imports
import System.Environment ( getArgs )
import System.Exit        ( exitFailure)
import System.IO          ( hPrint, stderr )

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

  print i `catchImpossible` \e →
    do hPrint stderr e
       exitFailure

  printTypes i `catchImpossible` \e →
    do hPrint stderr e
       exitFailure
