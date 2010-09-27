------------------------------------------------------------------------------
-- The product data type
------------------------------------------------------------------------------

module LTC.Data.Product where

open import LTC.Minimal.Core using ( D )

infixr 4 _,_

------------------------------------------------------------------------------

-- See Lib.Data.Product for the conjunction.

-- ∃D : (D → Set) → Set
-- ∃D P = ∃ P

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _ ) = x

∃D-proj₂ : {P : D → Set} → (x-px : ∃D P) → P (∃D-proj₁ x-px)
∃D-proj₂ (_ , px) = px
