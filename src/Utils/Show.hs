------------------------------------------------------------------------------
-- Utilities related to show
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Show ( showListLn, showLn ) where

------------------------------------------------------------------------------

showLn ∷ Show a ⇒ a → String
showLn = (++ "\n") . show

-- | Show version on lists where the elements are separated by newline
-- characters.
showListLn ∷ Show a ⇒ [a] → String
showListLn xs = xs >>= showLn  -- From Autoproc.Procmail.
