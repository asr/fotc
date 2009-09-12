module Monad where

import Control.Monad.Reader ( ReaderT )

import Options ( Options )

-- The environmet 'Vars' represents the names of variables bounded in the Agda
-- types.

type Vars = [String]

initialVars :: Vars
initialVars = []

{-| The translation monad from Agda types to FOL formulas
-}
type T a = ReaderT (Options, Vars) IO a
