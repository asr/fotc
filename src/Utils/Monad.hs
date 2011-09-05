------------------------------------------------------------------------------
-- Utilities on monads
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Monad ( whenM ) where

import Control.Monad ( when )

------------------------------------------------------------------------------
-- | Lifted version of 'when'.
whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM p action = p >>= \b → when b action
