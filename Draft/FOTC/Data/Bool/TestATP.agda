------------------------------------------------------------------------------
-- Testing
------------------------------------------------------------------------------

module Draft.FOTC.Data.Bool.TestATP where

open import FOTC.Base

open import FOTC.Data.Bool.Type

------------------------------------------------------------------------------

postulate
  thm : ∀ {b}(P : D → Set) → (Bool b ∧ P true ∧ P false) → P b
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm #-}

postulate
  thm₁ : ∀ {P : D → Set}{x y z} → Bool x → P y → P z → P (if x then y else z)
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm₁ #-}

Bool-elim : ∀ (P : D → Set){x y z} → Bool x → P y → P z →
            P (if x then y else z)
Bool-elim P {y = y} tB Py Pz = subst P (sym (if-true y)) Py
Bool-elim P {z = z} fB Py Pz = subst P (sym (if-false z)) Pz

_&&_ : D → D → D
x && y = if x then y else false
{-# ATP definition _&&_ #-}

postulate
  &&-Bool : ∀ {x y} → Bool x → Bool y → Bool (x && y)
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove &&-Bool Bool-elim #-}

&&-Bool₁ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₁ {y = y} tB By = prf
  where
    postulate prf : Bool (true && y)
    {-# ATP prove prf Bool-elim #-}
&&-Bool₁ {y = y} fB By = prf
  where
    postulate prf : Bool (false && y)
    {-# ATP prove prf Bool-elim #-}

&&-Bool₂ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₂ tB By = Bool-elim Bool tB By fB
&&-Bool₂ fB By = Bool-elim Bool fB By fB
