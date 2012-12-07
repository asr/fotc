------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.Division.IsCorrect where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Program.Division.ConversionRules
open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.Specification

------------------------------------------------------------------------------
-- The division result is correct when the dividend is less than
-- the divisor.

div-x<y-helper : ∀ {i j} → N i → N j → i < j → i ≡ j * div i j + i
div-x<y-helper {i} {j} Ni Nj i<j = sym prf
  where
  prf : j * div i j + i ≡ i
  prf = j * div i j + i ≡⟨ +-leftCong (*-rightCong (div-x<y i<j)) ⟩
        j * zero + i    ≡⟨ +-leftCong (*-rightZero Nj) ⟩
        zero + i        ≡⟨ +-leftIdentity i ⟩
        i               ∎

div-x<y-correct : ∀ {i j} → N i → N j → i < j →
                  ∃[ r ] N r ∧ r < j ∧ i ≡ j * div i j + r
div-x<y-correct Ni Nj i<j = _ , Ni , i<j , div-x<y-helper Ni Nj i<j

-- The division result is correct when the dividend is greater or equal
-- than the divisor.
--
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

div-x≮y-helper : ∀ {i j r} → N i → N j → N r →
                 i ≮ j →
                 i ∸ j ≡ j * div (i ∸ j) j + r →
                 i ≡ j * div i j + r
div-x≮y-helper {i} {j} {r} Ni Nj Nr i≮j helperH =
  i                             ≡⟨ helper Ni Nj Nr helperH ⟩
  j * succ₁ (div (i ∸ j) j) + r ≡⟨ prf ⟩
  j * div i j + r               ∎
  where
  prf : j * succ₁ (div (i ∸ j) j) + r ≡ j * div i j + r
  prf = subst (λ x → j * x + r ≡ j * div i j + r)
              (div-x≮y i≮j)
              refl

div-x≮y-correct : ∀ {i j} → N i → N j →
                  (DIV (i ∸ j) j (div (i ∸ j) j)) →
                  i ≮ j →
                  ∃[ r ] N r ∧ r < j ∧ i ≡ j * div i j + r
div-x≮y-correct {i} {j} Ni Nj (h₁ , r , r-correct) i≮j =
  r , Nr , r<j , div-x≮y-helper Ni Nj Nr i≮j helperH
  where
  Nr : N r
  Nr = ∧-proj₁ r-correct

  r<j : r < j
  r<j = ∧-proj₁ (∧-proj₂ r-correct)

  helperH : i ∸ j ≡ j * div (i ∸ j) j + r
  helperH = ∧-proj₂ (∧-proj₂ r-correct)
