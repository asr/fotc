------------------------------------------------------------------------------
-- Testing polymorphic lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-propositional-functions #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Polymorphism.List where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------

-- NB. The data type list is in *Set₁*.
data List (A : D → Set) : D → Set₁ where
  lnil  :                              List A []
  lcons : ∀ {x xs} → A x → List A xs → List A (x ∷ xs)
{-# ATP axiom lnil lcons #-}

postulate foo : ∀ x → x ≡ x
{-# ATP prove foo #-}
