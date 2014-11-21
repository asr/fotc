------------------------------------------------------------------------------
-- Parametrized preorder reasoning
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Common.Relation.Binary.PreorderReasoning
  {D     : Set}
  (_∼_   : D → D → Set)
  (refl  : ∀ {x} → x ∼ x)
  (trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z)
  where

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Relation.Binary.PreorderReasoning).
infixr 5 _∼⟨_⟩_
infix  5 _∎

------------------------------------------------------------------------------
-- From (Mu, S.-C., Ko, H.-S. and Jansson, P. (2009)).
--
-- N.B. Unlike Ulf's thesis (and the Agda standard library 0.8.1) this
-- set of combinators do not use a wrapper data type.

_∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
_ ∼⟨ x∼y ⟩ y∼z = trans x∼y y∼z

_∎ : ∀ x → x ∼ x
_∎ _ = refl

------------------------------------------------------------------------------
-- References
--
-- Mu, S.-C., Ko, H.-S. and Jansson, P. (2009). Algebra of programming
-- in Agda: Dependent types for relational program derivation. Journal
-- of Functional Programming 19.5, pp. 545–579.
