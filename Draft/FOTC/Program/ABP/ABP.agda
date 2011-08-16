------------------------------------------------------------------------------
-- The alternating bit protocol (ABP)
------------------------------------------------------------------------------

-- This module define the ABP following the presentation in [1].

-- [1] Peter Dybjer and Herbert Sander. A functional programming
--     approach to the specification and verification of concurrent
--     systems. Formal Aspects of Computing, 1:303–319, 1989.

module Draft.FOTC.Program.ABP.ABP where

open import FOTC.Base

open import FOTC.Data.Bool
open import FOTC.Data.Stream.Type

open import Draft.FOTC.Program.ABP.Fair
open import Draft.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- ABP equations

postulate
  abpsend               : D → D → D → D
  await                 : D → D → D → D → D
  abpack abpout corrupt : D → D → D

  abpsend-eq   : ∀ b i is ds →
                 abpsend b (i ∷ is) ds ≡ < i , b > ∷ await b i is ds

  await-ok≡    : ∀ b b₀ i is ds →
                 b ≡ b₀ →
                 await b i is (ok b₀ ∷ ds) ≡ abpsend (not b) is ds

  await-ok≠    : ∀ b b₀ i is ds →
                 ¬ (b ≡ b₀) →
                 await b i is (ok b₀ ∷ ds) ≡ < i , b > ∷ await b i is ds

  await-error  : ∀ b i is ds →
                 await b i is (error ∷ ds) ≡ < i , b > ∷ await b i is ds

  abpack-ok≡   : ∀ b b₀ i bs →
                 b ≡ b₀ →
                 abpack b (ok < i , b₀ > ∷ bs) ≡ b ∷ abpack (not b) bs

  abpack-ok≠   : ∀ b b₀ i bs →
                 ¬ (b ≡ b₀) →
                 abpack b (ok < i , b₀ > ∷ bs) ≡ not b ∷ abpack b bs

  abpack-error : ∀ b bs → abpack b (error ∷ bs) ≡ not b ∷ abpack b bs

  abpout-ok≡   : ∀ b b₀ i bs →
                 b ≡ b₀ →
                 abpout b (ok < i , b₀ > ∷ bs) ≡ i ∷ abpout (not b) bs

  abpout-ok≠   : ∀ b b₀ i bs →
                 ¬ (b ≡ b₀) →
                 abpout b (ok < i , b₀ > ∷ bs) ≡ abpout b bs

  abpout-error : ∀ b bs → abpout b (error ∷ bs) ≡ abpout b bs

  corrupt-L    : ∀ os x xs → corrupt (L ∷ os) (x ∷ xs) ≡ ok x ∷ corrupt os xs
  corrupt-O    : ∀ os x xs → corrupt (O ∷ os) (x ∷ xs) ≡ error ∷ corrupt os xs

postulate
  has hbs hcs hds transfer :
    (D → D → D) → (D → D) → (D → D) → (D → D) → (D → D) → D → D

  has-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
           has f₁ f₂ f₃ g₁ g₂ is ≡ f₁ is (hds f₁ f₂ f₃ g₁ g₂ is)

  hbs-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
           hbs f₁ f₂ f₃ g₁ g₂ is ≡ g₁ (has f₁ f₂ f₃ g₁ g₂ is)

  hcs-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
           hcs f₁ f₂ f₃ g₁ g₂ is ≡ f₂ (hbs f₁ f₂ f₃ g₁ g₂ is)

  hds-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
           hds f₁ f₂ f₃ g₁ g₂ is ≡ g₂ (hcs f₁ f₂ f₃ g₁ g₂ is)

  transfer-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                transfer f₁ f₂ f₃ g₁ g₂ is ≡ f₃ (hbs f₁ f₂ f₃ g₁ g₂ is)

postulate
  abptrans    : D → D → D → D → D
  abptrans-eq :
    ∀ b os₀ os₁ is → abptrans b os₀ os₁ is ≡
    transfer (abpsend b) (abpack b) (abpout b) (corrupt os₀) (corrupt os₁) is

------------------------------------------------------------------------------
-- ABP relations

-- Abbreviation for the recursive equations of the alternating bit
-- protocol.
Abp : D → D → D → D → D → D → D → D → D → Set
Abp b is os₀ os₁ as bs cs ds js =
  as ≡ abpsend b is ds
  ∧ bs ≡ corrupt os₀ as
  ∧ cs ≡ abpack b bs
  ∧ ds ≡ corrupt os₁ cs
  ∧ js ≡ abpout b bs

Abp' : D → D → D → D → D → D → D → D → D → D → Set
Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' =
  ds' ≡ corrupt os₁' (b ∷ cs')
  ∧ as' ≡ await b i' is' ds'  -- Typo in ds'.
  ∧ bs' ≡ corrupt os₀' as'
  ∧ cs' ≡ abpack (not b) bs'
  ∧ js' ≡ abpout (not b) bs'

-- Auxiliary bisimulation.
_B_ : D → D → Set
is B js = ∃ λ b → ∃ λ os₀ → ∃ λ os₁ → ∃ λ as → ∃ λ bs → ∃ λ cs → ∃ λ ds →
          Stream is
          ∧ Bit b
          ∧ Fair os₀
          ∧ Fair os₁
          ∧ Abp b is os₀ os₁ as bs cs ds js
