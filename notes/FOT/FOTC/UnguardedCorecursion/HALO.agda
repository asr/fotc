------------------------------------------------------------------------------
-- Testing a non-admissible property from the HALO paper
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Vytiniotis, D., Peyton Jones, S., Rosén, D. and Claessen,
--   K. (2013). HALO: Haskell to Logic thorugh Denotational
--   Semantics. In: Proceedings of the 40th annual ACM SIGPLAN-SIGACT
--   symposium on Principles of programming languages (POPL’13),
--   pp. 431–442.

module FOT.FOTC.UnguardedCorecursion.HALO where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Stream.Equality.PropertiesI
open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI

------------------------------------------------------------------------------
-- The HALO paper states the property
--
-- ∀ x . f x ≠ ones
--
-- cannot be proved because it is a non-admissible predicate.

postulate
  ones    : D
  ones-eq : ones ≡ succ₁ zero ∷ ones

postulate
  f     : D → D
  f-eq₁ : ∀ n → f (succ₁ n) ≡ succ₁ zero ∷ f n
  f-eq₂ : f zero ≡ zero ∷ []

-- A proof using the bisimilarity relation relation.
thm : ∀ {n} → N n → f n ≉ ones
thm nzero h with ≈-unf h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = 0≢S (trans (sym x'≡0) x'≡1)
  where
  x'≡0 : x' ≡ zero
  x'≡0 = ∧-proj₁ (∷-injective (trans (sym prf₁) f-eq₂))

  x'≡1 : x' ≡ succ₁ zero
  x'≡1 = ∧-proj₁ (∷-injective (trans (sym prf₂) ones-eq))

thm (nsucc {n} Nn) h with ≈-unf h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = thm Nn (∷-injective≈ helper)
  where
  xs'≡fn : xs' ≡ f n
  xs'≡fn = ∧-proj₂ (∷-injective (trans (sym prf₁) (f-eq₁ n)))

  ys'≡ones : ys' ≡ ones
  ys'≡ones = ∧-proj₂ (∷-injective (trans (sym prf₂) ones-eq))

  helper : x' ∷ f n ≈ x' ∷ ones
  helper = ≈-pre-fixed ( x'
                       , xs'
                       , ys'
                       , ∷-rightCong (sym xs'≡fn)
                       , ∷-rightCong (sym ys'≡ones)
                       , prf₃
                       )

-- A proof using the propositional equality.
thm' : ∀ {n} → N n → f n ≢ ones
thm' nzero h = 0≢S (∧-proj₁ (∷-injective helper))
  where
  helper : zero ∷ [] ≡ succ₁ zero ∷ ones
  helper = trans₂ (sym f-eq₂) h ones-eq

thm' (nsucc {n} Nn) h = thm' Nn (∧-proj₂ (∷-injective helper))
  where
  helper : succ₁ zero ∷ f n ≡ succ₁ zero ∷ ones
  helper = trans₂ (sym (f-eq₁ n)) h ones-eq
