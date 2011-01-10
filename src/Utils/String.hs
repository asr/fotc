{-# LANGUAGE UnicodeSyntax #-}

module Utils.String ( replace ) where

------------------------------------------------------------------------------
-- | Replace the first argument by the second one on the string.
replace ∷ Char → Char → String → String
replace _   _    []       = []
replace src dest (x : xs) =
    if src == x
    then dest : replace src dest xs
    else x    : replace src dest xs
