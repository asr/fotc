------------------------------------------------------------------------------
-- FOCT list terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Base.List.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- Congruence properties

postulate ∷-leftCong : ∀ {x y xs} → x ≡ y → x ∷ xs ≡ y ∷ xs
{-# ATP prove ∷-leftCong #-}

postulate ∷-rightCong : ∀ {x xs ys} → xs ≡ ys → x ∷ xs ≡ x ∷ ys
{-# ATP prove ∷-rightCong #-}

postulate ∷-Cong : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
{-# ATP prove ∷-Cong #-}

postulate headCong : ∀ {xs ys} → xs ≡ ys → head₁ xs ≡ head₁ ys
{-# ATP prove headCong #-}

postulate tailCong : ∀ {xs ys} → xs ≡ ys → tail₁ xs ≡ tail₁ ys
{-# ATP prove tailCong #-}

------------------------------------------------------------------------------
-- Injective properties

postulate ∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}
