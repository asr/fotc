------------------------------------------------------------------------------
-- Axiomatic PA propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEquality where

open import Combined.PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------
-- Identity properties

postulate ≈-refl : ∀ {n} → n ≈ n
{-# ATP prove ≈-refl #-}

postulate ≈-sym : ∀ {m n} → m ≈ n → n ≈ m
{-# ATP prove ≈-sym #-}

postulate ≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
{-# ATP prove ≈-trans #-}
