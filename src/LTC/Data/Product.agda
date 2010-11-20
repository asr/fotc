------------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------------

module LTC.Data.Product where

open import LTC.Base.Core using ( D )

infixr 7 _,_

------------------------------------------------------------------------------
-- See Lib.Data.Product for the conjunction.

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _) = x

∃D-proj₂ : {P : D → Set}(∃p : ∃D P) → P (∃D-proj₁ ∃p)
∃D-proj₂ (_ , px) = px
