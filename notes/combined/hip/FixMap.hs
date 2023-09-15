
module FixMap where

import Prelude hiding ( map )

fix :: (a -> a) -> a
fix f = f (fix f)

map :: (a -> b) -> [a] -> [b]
map _ []       = []
map f (x : xs) = f x : map f xs

mapF :: ((a -> b) -> [a] -> [b]) -> (a -> b) -> [a] -> [b]
mapF _ _ []       = []
mapF m f (x : xs) = f x : m f xs

map' :: (a -> b) -> [a] -> [b]
map' = fix mapF
