------------------------------------------------------------------------------
-- Utilities related to show
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Show where

------------------------------------------------------------------------------

class MyShow a where
  myShow ∷ a → String

-- | Show version on lists where the elements are separated by newline
-- characters.
instance Show a ⇒ MyShow [a] where
  myShow []       = []
  myShow (x : xs) = show x ++ "\n" ++ myShow xs
