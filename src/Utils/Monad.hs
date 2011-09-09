------------------------------------------------------------------------------
-- Utilities on monads
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Monad ( unlessM, whenM ) where

import Control.Monad ( unless, when )

------------------------------------------------------------------------------
-- | Lifted version of 'when'.
whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM p action = p >>= \b → when b action

-- | Lifted version of 'unless'.
unlessM ∷ Monad m ⇒ m Bool → m () → m ()
unlessM p action = p >>= \b → unless b action
