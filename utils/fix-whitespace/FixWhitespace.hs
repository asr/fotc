-- Adapted from Agda sources.

{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

import Control.Monad                  ( when )
import Data.Char as Char              ( isSpace )
import Data.Text                      ( Text )
import qualified Data.Text as Text    ( dropWhileEnd, lines, null, unlines )
import qualified Data.Text.IO as Text ( hGetContents, hPutStr ) -- Strict IO.
import System.Environment             ( getArgs )
import System.Exit                    ( exitFailure )
import System.FilePath.Find           ( (||?), (==?), always, extension, find )

import System.IO
  ( hPutStr
  , hSetEncoding
  , IOMode(ReadMode, WriteMode)
  , stderr
  , utf8
  , withFile
  )

------------------------------------------------------------------------------
-- Configuration parameters.

extensions ∷ [String]
extensions =
  [ ".agda"
  , ".cabal"
  , ".el"
  , ".hs"
  , ".hs-boot"
  , ".thy"
  , ".txt"
  , ".tptp"
  , ".v"
  , ".x"
  , ".y"
  ]

srcDir ∷ String
srcDir = "."

-- Modes.

data Mode
  = Fix    -- ^ Fix whitespace issues.
  | Check  -- ^ Check if there are any whitespace issues.
    deriving Eq

main ∷ IO ()
main = do
  args ← getArgs
  mode ← case args of
    []          → return Fix
    ["--check"] → return Check
    _           → hPutStr stderr usage >> exitFailure

  changes ←
    mapM (fix mode) =<<
      find always (foldr1 (||?) $ map (extension ==?) extensions) srcDir

  when (or changes && mode == Check) exitFailure

-- | Usage info.

usage ∷ String
usage = unlines
  [ "fix-whitespace: Fixes whitespace issues for Agda sources."
  , ""
  , "Usage: fix-whitespace [--check]"
  , ""
  , "This program should be run in the base directory."
  , ""
  , "By default the program does the following for every"
  , list extensions ++ " file under " ++ srcDir ++ ":"
  , "* Removes trailing whitespace."
  , "* Removes trailing lines containing nothing but whitespace."
  , "* Ensures that the file ends in a newline character."
  , ""
  , "With the --check flag the program does not change any files,"
  , "it just checks if any files would have been changed. In this"
  , "case it returns with a non-zero exit code."
  , ""
  , "Background: Agda was reported to fail to compile on Windows"
  , "because a file did not end with a newline character (Agda"
  , "uses -Werror)."
  ]

  where
  list ∷ [String] → String
  list [x]      = x
  list [x, y]   = x ++ " and " ++ y
  list (x : xs) = x ++ ", " ++ list xs
  list _        = error "Impossible list"

-- | Fix a file. Only performs changes if the mode is 'Fix'. Returns
-- 'True' iff any changes would have been performed in the 'Fix' mode.

fix ∷ Mode → FilePath → IO Bool
fix mode f = do
  new ← withFile f ReadMode $ \h → do
    hSetEncoding h utf8
    s ← Text.hGetContents h
    let s' = transform s
    return $ if s' == s then Nothing else Just s'
  case new of
    Nothing → return False
    Just s  → do
      putStrLn $ "Whitespace violation "
                 ++ (if mode == Fix then "fixed" else "detected")
                 ++ " in " ++ f
      when (mode == Fix) $
        withFile f WriteMode $ \h → do
          hSetEncoding h utf8
          Text.hPutStr h s
      return True

-- | Transforms the contents of a file.
transform ∷ Text → Text
transform =
  Text.unlines .
  removeFinalEmptyLines .
  map removeTrailingWhitespace .
  Text.lines

  where
  removeFinalEmptyLines ∷ [Text] → [Text]
  removeFinalEmptyLines = reverse . dropWhile Text.null . reverse

  removeTrailingWhitespace ∷ Text → Text
  removeTrailingWhitespace = Text.dropWhileEnd Char.isSpace
