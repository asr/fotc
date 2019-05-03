{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module DiscriminationRules where

open import Data.Bool.Base
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

true≢false : true ≢ false
true≢false ()

0≠suc : ∀ {n} → 0 ≢ suc n
0≠suc ()

[]≢x∷xs : {A : Set}{x : A}{xs : List A} → [] ≢ x ∷ xs
[]≢x∷xs ()
