------------------------------------------------------------------------------
-- Testing polymorphic lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-propositional-functions #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Polymorphism.List where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Heterogeneous lists
data List : D → Set where
  lnil  :                      List []
  lcons : ∀ x {xs} → List xs → List (x ∷ xs)

-- Lists of total natural numbers
data ListN : D → Set where
  lnnil  :                             ListN []
  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

-- Lists of total Booleans
data ListB : D → Set where
  lbnil  :                                ListB []
  lbcons : ∀ {b bs} → Bool b → ListB bs → ListB (b ∷ bs)

-- Polymorphic lists.
-- NB. The data type list is in *Set₁*.
data ListP (A : D → Set) : D → Set₁ where
  lnil  :                               ListP A []
  lcons : ∀ {x xs} → A x → ListP A xs → ListP A (x ∷ xs)

List₁ : D → Set₁
List₁ = ListP (λ d → d ≡ d)

ListN₁ : D → Set₁
ListN₁ = ListP N

ListB₁ : D → Set₁
ListB₁ = ListP Bool
