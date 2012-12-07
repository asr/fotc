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

postulate div-x<y-helper : ∀ {i j} → N i → N j → i < j → i ≡ j * div i j + i
{-# ATP prove div-x<y-helper *-rightZero #-}

div-x<y-correct : ∀ {i j} → N i → N j → i < j →
                  ∃[ r ] N r ∧ r < j ∧ i ≡ j * div i j + r
div-x<y-correct Ni Nj i<j = _ , Ni , i<j , div-x<y-helper Ni Nj i<j

-- The division result is correct when the dividend is greater or equal
-- than the divisor.
-- Using the inductive hypothesis ih we know that
--
-- i ∸ j = j * (div (i ∸ j) j) + r.

-- From that we get
--
-- i = j * (succ (div (i ∸ j) j)) + r, and we know
--
-- div i j = succ (div (i ∸ j) j) therefore we get
--
-- i = j * div i j + r.
postulate helper : ∀ {i j r} → N i → N j → N r →
                   i ∸ j ≡ j * div (i ∸ j) j + r →
                   i ≡ j * succ₁ (div (i ∸ j) j) + r

postulate div-x≮y-helper : ∀ {i j r} → N i → N j → N r →
                           i ≮ j →
                           i ∸ j ≡ j * div (i ∸ j) j + r →
                           i ≡ j * div i j + r
{-# ATP prove div-x≮y-helper helper #-}

postulate div-x≮y-correct : ∀ {i j} → N i → N j →
                            (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
                            i ≮ j →
                            ∃[ r ] N r ∧ r < j ∧ i ≡ j * div i j + r
{-# ATP prove div-x≮y-correct div-x≮y-helper #-}
