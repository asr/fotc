------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Division.IsCorrectATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Program.Division.Division
open import FOTC.Program.Division.Specification

------------------------------------------------------------------------------
-- The division result is correct when the dividend is less than
-- the divisor.

postulate div-x<y-helper : ∀ {i j} → N i → N j → LT i j → i ≡ j * div i j + i
{-# ATP prove div-x<y-helper +-leftIdentity *-rightZero #-}

div-x<y-correct : ∀ {i j} → N i → N j → LT i j →
                  ∃[ r ] N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x<y-correct {i} Ni Nj i<j = ∃-intro (Ni , i<j , div-x<y-helper Ni Nj i<j)

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
           i ≡ j * succ₁ (div (i ∸ j) j) + r

postulate
  div-x≮y-helper : ∀ {i j r} → N i → N j → N r →
                   NLT i j →
                   i ∸ j ≡ j * div (i ∸ j) j + r →
                   i ≡ j * div i j + r
{-# ATP prove div-x≮y-helper helper #-}

-- TODO: To test an ATP proof.
-- 2012-02-29: We are using the existential witness only for
-- documenting the types in the where clause. They could be removed.
div-x≮y-correct : ∀ {i j} → N i → N j →
                  (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
                  NLT i j →
                  ∃[ r ] N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x≮y-correct {i} {j} Ni Nj (h₁ , ∃-intro {r} r-correct) i≮j =
  ∃-intro (Nr , r<j , div-x≮y-helper Ni Nj Nr i≮j helperH)
  where
  Nr : N r
  Nr = ∧-proj₁ r-correct

  r<j : LT r j
  r<j = ∧-proj₁ (∧-proj₂ r-correct)

  helperH : i ∸ j ≡ j * div (i ∸ j) j + r
  helperH = ∧-proj₂ (∧-proj₂ r-correct)
