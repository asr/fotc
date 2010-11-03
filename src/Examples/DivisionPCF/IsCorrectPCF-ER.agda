------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsCorrectPCF-ER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import Examples.DivisionPCF.DivisionPCF using ( div )
open import Examples.DivisionPCF.EquationsPCF-ER using ( div-x<y ; div-x≥y )
open import Examples.DivisionPCF.SpecificationPCF using ( DIV )

import Lib.Relation.Binary.EqReasoning
open module IsCorrectPCF-ER =
  Lib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import LTC-PCF.DataPCF.NatPCF using ( _+_ ; _-_ ; _*_ ; N )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( GE ; LT )
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF-ER
  using ( +-leftIdentity
        ; *-rightZero
        )

------------------------------------------------------------------------------
-- The division result is correct when the dividend is less than
-- the divisor.

div-x<y-aux : {i j : D} → N i → N j → LT i j → i ≡ j * (div i j) + i
div-x<y-aux {i} {j} Ni Nj i<j = sym
    ( begin
        j * (div i j) + i ≡⟨ prf₁ ⟩
        j * zero + i      ≡⟨ prf₂ ⟩
        zero + i          ≡⟨ +-leftIdentity Ni ⟩
        i
      ∎
    )
    where
      prf₁ : j * (div i j) + i ≡ j * zero + i
      prf₁ = subst (λ x → j * x + i ≡ j * zero + i)
                   (sym (div-x<y i<j))
                   refl

      prf₂ : j * zero + i ≡ zero + i
      prf₂ = subst (λ x → x + i ≡ zero + i)
                   (sym (*-rightZero Nj))
                   refl

div-x<y-correct : {i j : D} → N i → N j → LT i j →
                  (∃D (λ r → N r ∧ LT r j ∧ i ≡ j * (div i j) + r))
div-x<y-correct {i} Ni Nj i<j = i , Ni , i<j , div-x<y-aux Ni Nj i<j

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

div-x≥y-aux : {i j r : D} → N i → N j → N r →
              GE i j →
              i - j ≡ j * (div (i - j) j) + r →
              i ≡ j * (div i j) + r
div-x≥y-aux {i} {j} {r} Ni Nj Nr i≥j auxH =
  begin
    i ≡⟨ aux Ni Nj Nr auxH ⟩
    j * succ (div (i - j) j) + r ≡⟨ prf ⟩
    j * (div i j) + r
  ∎

  where
    prf : j * succ (div (i - j) j) + r ≡ j * (div i j) + r
    prf = subst (λ x → j * x + r ≡ j * (div i j) + r)
                (div-x≥y Ni Nj i≥j )
                refl

div-x≥y-correct : {i j : D} → N i → N j →
                  (ih : DIV (i - j) j (div (i - j) j)) →
                  GE i j →
                  ∃D (λ r → (N r) ∧ (LT r j) ∧ (i ≡ j * (div i j) + r))
div-x≥y-correct {i} {j} Ni Nj ih i≥j =
  r , Nr , r<j , div-x≥y-aux Ni Nj Nr i≥j auxH

  where
    -- The parts of the inductive hipothesis ih.
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
