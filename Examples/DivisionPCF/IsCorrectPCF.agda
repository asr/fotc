------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsCorrectPCF where

open import LTC.Minimal

open import Examples.DivisionPCF.DivisionPCF
open import Examples.DivisionPCF.EquationsPCF
open import Examples.DivisionPCF.SpecificationPCF

open import LTC.Data.NatPCF
open import LTC.Data.NatPCF.InequalitiesPCF
open import LTC.Data.NatPCF.PropertiesPCF

------------------------------------------------------------------------------

-- The division result is correct when the dividend is less than
-- the divisor.

postulate
  div-x<y-aux : {i j : D} → N i → N j → LT i j → i ≡ j * (div i j) + i
{-# ATP prove div-x<y-aux  +-leftIdentity *-rightZero div-x<y #-}

div-x<y-correct : {i j : D} → N i → N j → LT i j →
                  (∃D (λ r → N r ∧ LT r j ∧ i ≡ j * (div i j) + r))
div-x<y-correct {i} Ni Nj i<j =
  i , (Ni , (i<j , (div-x<y-aux Ni Nj i<j)))

-- The division result is correct when the dividend is greater or equal
-- than the divisor.
-- Using the inductive hypothesis 'ih' we know that
-- 'i - j = j * (div (i - j) j) + r'. From
-- that we get 'i = j * (succ (div (i - j) j)) + r', and
-- we know 'div i j = succ (div (i - j) j); therefore we
-- get 'i = j * div i j + r'.

postulate
  aux : {i j r : D} → N i → N j → N r →
        i - j ≡ j * (div (i - j) j) + r →
        i ≡ j * succ (div (i - j) j) + r

postulate
  div-x≥y-aux : {i j r : D} → N i → N j → N r →
                GE i j →
                i - j ≡ j * (div (i - j) j) + r →
                i ≡ j * (div i j) + r
{-# ATP prove div-x≥y-aux div-x≥y aux #-}

div-x≥y-correct : {i j : D} → N i → N j →
                  (ih : DIV (i - j) j (div (i - j) j)) →
                  GE i j →
                  ∃D (λ r → (N r) ∧ (LT r j) ∧ (i ≡ j * (div i j) + r))
div-x≥y-correct {i} {j} Ni Nj ih i≥j =
  r , (Nr , (r<j , (div-x≥y-aux Ni Nj Nr i≥j auxH)))

    where
      -- The parts of the inductive hipothesis ih
      r : D
      r = ∃D-proj₁ (∧-proj₂ ih)

      r-correct : N r ∧ LT r j ∧ i - j ≡ j * (div (i - j) j) + r
      r-correct = ∃D-proj₂ (∧-proj₂ ih)

      Nr : N r
      Nr = ∧-proj₁ r-correct

      r<j : LT r j
      r<j = ∧-proj₁ (∧-proj₂ r-correct)

      auxH : i - j ≡ j * (div (i - j) j) + r
      auxH = ∧-proj₂ (∧-proj₂ r-correct)
