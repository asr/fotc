module Logic where

infix  30 _==_

postulate
  D    : Set
  _==_ : D -> D -> Set

import LogicalConstants
open module LC = LogicalConstants D

postulate

 f10 : (A : Set)   -> A Implies A
 f20 : (A B : Set) -> A And B Implies B And A
 f30 : (A : Set)   -> Not (A And True) Equiv (Not A Or False)
 f40 : (d : D)     -> d == d
 f50 : (d1 d2 : D) -> (d1 == d2) Implies (d2 == d1)

 f60 : ForAll (\(x : D) -> x == x)
 f70 : (x : D) -> x == x
 f80 : ForAll (\(x : D) -> Exists (\(y : D) ->  x == y))

{-# EXTERNAL Equinox f10 #-}
{-# EXTERNAL Equinox f20 #-}
{-# EXTERNAL Equinox f30 #-}
{-# EXTERNAL Equinox f40 #-}
{-# EXTERNAL Equinox f50 #-}
{-# EXTERNAL Equinox f60 #-}
{-# EXTERNAL Equinox f70 #-}
{-# EXTERNAL Equinox f80 #-}
