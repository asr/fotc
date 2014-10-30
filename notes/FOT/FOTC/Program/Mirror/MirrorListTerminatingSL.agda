------------------------------------------------------------------------------
-- Terminating mirror function
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Mirror.MirrorListTerminatingSL where

open import Data.List

------------------------------------------------------------------------------
-- The rose tree type.
data Tree (A : Set) : Set where
  tree : A → List (Tree A) → Tree A

------------------------------------------------------------------------------
-- An alternative and terminating definition of mirror. Adapted from
-- http://stackoverflow.com/questions/9146928/termination-of-structural-induction

-- The mirror function.
mirror       : {A : Set} → Tree A → Tree A
mirrorBranch : {A : Set} → List (Tree A) → List (Tree A)

mirror       (tree a ts) = tree a (reverse (mirrorBranch ts))
mirrorBranch []          = []
mirrorBranch (t ∷ ts)    = mirror t ∷ mirrorBranch ts
