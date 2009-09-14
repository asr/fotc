-- Test the translation of functions with holes

module Holes where

infix  30 _==_
infix  60 if_then_else_
infixl 60 _+_

postulate
  D             : Set
  true          : D
  _==_          : D -> D -> Set

  _+_           : D -> D -> D
  if_then_else_ : D -> D -> D -> D

  -- Using a function with two holes
  comm : (a b : D) -> a + b == b + a

  -- Using a function with three holes
  CB₁ : (a b : D) -> if true then a else b == a

{-# EXTERNAL Equinox comm #-}
{-# EXTERNAL Equinox CB₁ #-}
