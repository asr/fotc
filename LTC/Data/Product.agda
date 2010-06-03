------------------------------------------------------------------------------
-- The existential quantifier type on D
------------------------------------------------------------------------------

module LTC.Data.Product where

open import LTC.Minimal.Core
-- open import MyStdLib.Data.Product

------------------------------------------------------------------------------
infixr 4 _,_

-- ∃D : (D → Set) → Set
-- ∃D P = ∃ P

data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _ ) = x

∃D-proj₂ : {P : D → Set} → (x-px : ∃D P) → P (∃D-proj₁ x-px)
∃D-proj₂ (_ , px) = px
