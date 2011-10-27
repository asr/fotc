------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module FOTC.Program.Division.IsCorrectI where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Program.Division.Division
open import FOTC.Program.Division.EquationsI
open import FOTC.Program.Division.Specification

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- The division result is correct when the dividend is less than
-- the divisor.

div-x<y-helper : ∀ {i j} → N i → N j → LT i j → i ≡ j * div i j + i
div-x<y-helper {i} {j} Ni Nj i<j = sym
    ( begin
        j * div i j + i ≡⟨ prf₁ ⟩
        j * zero + i    ≡⟨ prf₂ ⟩
        zero + i        ≡⟨ +-leftIdentity Ni ⟩
        i
      ∎
    )
    where
    prf₁ : j * div i j + i ≡ j * zero + i
    prf₁ = subst (λ x → j * x + i ≡ j * zero + i)
                 (sym $ div-x<y i<j)
                 refl

    prf₂ : j * zero + i ≡ zero + i
    prf₂ = subst (λ x → x + i ≡ zero + i)
                 (sym $ *-rightZero Nj)
                 refl

div-x<y-correct : ∀ {i j} → N i → N j → LT i j →
                  ∃ λ r → N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x<y-correct {i} Ni Nj i<j = i , Ni , i<j , div-x<y-helper Ni Nj i<j

-- The division result is correct when the dividend is greater or equal
-- than the divisor.
-- Using the inductive hypothesis 'ih' we know that
-- 'i ∸ j = j * (div (i ∸ j) j) + r'. From
-- that we get 'i = j * (succ (div (i ∸ j) j)) + r', and
-- we know 'div i j = succ (div (i ∸ j) j); therefore we
-- get 'i = j * div i j + r'.

postulate
  helper : ∀ {i j r} → N i → N j → N r →
           i ∸ j ≡ j * div (i ∸ j) j + r →
           i ≡ j * succ₁ (div (i ∸ j) j) + r

div-x≮y-helper : ∀ {i j r} → N i → N j → N r →
                 NLT i j →
                 i ∸ j ≡ j * div (i ∸ j) j + r →
                 i ≡ j * div i j + r
div-x≮y-helper {i} {j} {r} Ni Nj Nr i≮j helperH =
  begin
    i                            ≡⟨ helper Ni Nj Nr helperH ⟩
    j * succ₁ (div (i ∸ j) j) + r ≡⟨ prf ⟩
    j * div i j + r
  ∎
  where
  prf : j * succ₁ (div (i ∸ j) j) + r ≡ j * div i j + r
  prf = subst (λ x → j * x + r ≡ j * div i j + r)
              (div-x≮y i≮j)
              refl

div-x≮y-correct : ∀ {i j} → N i → N j →
                  (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
                  NLT i j →
                  ∃ λ r → N r ∧ LT r j ∧ i ≡ j * div i j + r
div-x≮y-correct {i} {j} Ni Nj ih i≮j =
  r , Nr , r<j , div-x≮y-helper Ni Nj Nr i≮j helperH

  where
  -- The parts of the inductive hypothesis ih.
  r : D
  r = ∃-proj₁ (∧-proj₂ ih)

  r-correct : N r ∧ LT r j ∧ i ∸ j ≡ j * div (i ∸ j) j + r
  r-correct = ∃-proj₂ (∧-proj₂ ih)

  Nr : N r
  Nr = ∧-proj₁ r-correct

  r<j : LT r j
  r<j = ∧-proj₁ (∧-proj₂ r-correct)

  helperH : i ∸ j ≡ j * div (i ∸ j) j + r
  helperH = ∧-proj₂ (∧-proj₂ r-correct)
