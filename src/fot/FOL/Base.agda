------------------------------------------------------------------------------
-- First-order logic base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.Base where

infixr 3 _⇒_
infixr 2 _⇔_

------------------------------------------------------------------------------
-- First-order logic (without equality).
open import Common.FOL.FOL public

------------------------------------------------------------------------------
-- We added extra symbols for the implication, the bicondicional and
-- the universal quantification (see module Common.FOL.FOL).

-- The implication data type.
data _⇒_ (A B : Set) : Set where
  fun : (A → B) → A ⇒ B

app : {A B : Set} → A ⇒ B → A → B
app (fun f) a = f a

-- Biconditional.
_⇔_ : Set → Set → Set
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

-- The universal quantifier type on D.
data  ⋀ (A : D → Set) : Set where
  dfun : ((t : D) → A t) → ⋀ A

-- Sugar syntax for the universal quantifier.
syntax ⋀ (λ x → e) = ⋀[ x ] e

dapp : {A : D → Set}(t : D) → ⋀ A → A t
dapp t (dfun f) = f t

------------------------------------------------------------------------------
-- In first-order logic it is assumed that the universe of discourse
-- is nonempty.
postulate D≢∅ : D

------------------------------------------------------------------------------
-- The ATPs work in classical logic, therefore we add the principle of
-- the exclude middle for prove some non-intuitionistic theorems. Note
-- that we do not need to add the postulate as an ATP axiom.

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A
