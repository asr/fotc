------------------------------------------------------------------------------
-- Abelian group theory properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.GroupTheory.AbelianGroup.Properties where

open import Interactive.GroupTheory.AbelianGroup.Base

------------------------------------------------------------------------------

-- TODO (2019-06-09) : Missing proof.
postulate xyx⁻¹≡y : ∀ a b → a · b · a ⁻¹ ≡ b

-- TODO (2019-06-09) : Missing proof.
postulate x⁻¹y⁻¹≡[xy]⁻¹ : ∀ a b → a ⁻¹ · b ⁻¹ ≡ (a · b) ⁻¹
