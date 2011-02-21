------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.IsCorrectATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
  using ( _+_ ; _∸_ ; _*_
        ; N  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Inequalities using ( GE ; LT )
open import LTC-PCF.Data.Nat.PropertiesATP
  using ( +-leftIdentity
        ; *-rightZero
        )

open import LTC-PCF.Program.Division.Division using ( div )
open import LTC-PCF.Program.Division.EquationsATP using ( div-x<y ; div-x≥y )
open import LTC-PCF.Program.Division.Specification using ( DIV )

------------------------------------------------------------------------------
-- The division result is correct when the dividend is less than
-- the divisor.

postulate
  div-x<y-helper : ∀ {i j} → N i → N j → LT i j → i ≡ j * div i j + i
{-# ATP prove div-x<y-helper  +-leftIdentity *-rightZero div-x<y #-}

div-x<y-correct : ∀ {i j} → N i → N j → LT i j →
                  ∃D λ r → N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x<y-correct {i} Ni Nj i<j = i , Ni , i<j , div-x<y-helper Ni Nj i<j

-- The division result is correct when the dividend is greater or equal
-- than the divisor.
-- Using the inductive hypothesis 'ih' we know that
-- 'i ∸ j = j * div (i ∸ j) j + r'. From
-- that we get 'i = j * (succ (div (i ∸ j) j)) + r', and
-- we know 'div i j = succ (div (i ∸ j) j); therefore we
-- get 'i = j * div i j + r'.

postulate
  helper : ∀ {i j r} → N i → N j → N r →
           i ∸ j ≡ j * div (i ∸ j) j + r →
           i ≡ j * succ (div (i ∸ j) j) + r

postulate
  div-x≥y-helper : ∀ {i j r} → N i → N j → N r →
                   GE i j →
                   i ∸ j ≡ j * div (i ∸ j) j + r →
                   i ≡ j * div i j + r
-- E 1.2: CPU time limit exceeded (180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove div-x≥y-helper div-x≥y helper #-}

div-x≥y-correct : ∀ {i j} → N i → N j →
                  (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
                  GE i j →
                  ∃D λ r → N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x≥y-correct {i} {j} Ni Nj ih i≥j =
  r , Nr , r<j , div-x≥y-helper Ni Nj Nr i≥j helperH

  where
    -- The parts of the inductive hipothesis ih.
    r : D
    r = ∃D-proj₁ (∧-proj₂ ih)

    r-correct : N r ∧ LT r j ∧ i ∸ j ≡ j * div (i ∸ j) j + r
    r-correct = ∃D-proj₂ (∧-proj₂ ih)

    Nr : N r
    Nr = ∧-proj₁ r-correct

    r<j : LT r j
    r<j = ∧-proj₁ (∧-proj₂ r-correct)

    helperH : i ∸ j ≡ j * div (i ∸ j) j + r
    helperH = ∧-proj₂ (∧-proj₂ r-correct)
