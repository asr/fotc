------------------------------------------------------------------------------
-- Testing polymorphic lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Polymorphism.List where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- Heterogeneous lists
data List : D → Set where
  lnil  :                      List []
  lcons : ∀ x {xs} → List xs → List (x ∷ xs)

xs : D
xs = [0] ∷ true ∷ [1] ∷ false ∷ []

xs-List : List xs
xs-List = lcons [0] (lcons true (lcons [1] (lcons false lnil)))

-- Lists of total natural numbers
data ListN : D → Set where
  lnnil  :                             ListN []
  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

ys : D
ys = [0] ∷ [1] ∷ [2] ∷ []

ys-ListN : ListN ys
ys-ListN =
  lncons nzero (lncons (nsucc nzero) (lncons (nsucc (nsucc nzero)) lnnil))

-- Lists of total Booleans
data ListB : D → Set where
  lbnil  :                                ListB []
  lbcons : ∀ {b bs} → Bool b → ListB bs → ListB (b ∷ bs)

zs : D
zs = true ∷ false ∷ true ∷ []

zs-ListB : ListB zs
zs-ListB = lbcons btrue (lbcons bfalse (lbcons btrue lbnil))

-- Polymorphic lists.
-- NB. The data type list is in *Set₁*.
data ListP (A : D → Set) : D → Set₁ where
  lnil  :                               ListP A []
  lcons : ∀ {x xs} → A x → ListP A xs → ListP A (x ∷ xs)

List₁ : D → Set₁
List₁ = ListP (λ d → d ≡ d)

xs-List₁ : List₁ xs
xs-List₁ = lcons refl (lcons refl (lcons refl (lcons refl lnil)))

ListN₁ : D → Set₁
ListN₁ = ListP N

ys-ListN₁ : ListN₁ ys
ys-ListN₁ = lcons nzero (lcons (nsucc nzero) (lcons (nsucc (nsucc nzero)) lnil))

ListB₁ : D → Set₁
ListB₁ = ListP Bool

zs-ListB₁ : ListB₁ zs
zs-ListB₁ = lcons btrue (lcons bfalse (lcons btrue lnil))
