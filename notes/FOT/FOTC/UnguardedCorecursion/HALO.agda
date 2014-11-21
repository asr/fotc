------------------------------------------------------------------------------
-- Testing a non-admissible property from the HALO paper
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.UnguardedCorecursion.HALO where

-- open import Common.FOL.Relation.Binary.EqReasoning

-- open import FOTC.Base
-- open import FOTC.Base.List
-- open import FOTC.Base.List.PropertiesI
-- open import FOTC.Data.Conat
-- open import FOTC.Data.Conat.PropertiesI
-- open import FOTC.Data.Nat
-- open import FOTC.Data.Stream.Type
-- open import FOTC.Data.Stream.Equality.PropertiesI
-- open import FOTC.Relation.Binary.Bisimilarity.PropertiesI
-- open import FOTC.Relation.Binary.Bisimilarity.Type

-- ------------------------------------------------------------------------------
-- -- The HALO paper states the property
-- --
-- -- ∀ x . f x ≠ ones (1)
-- --
-- -- cannot be proved because it is a non-admissible one.

-- postulate
--   ones    : D
--   ones-eq : ones ≡ succ₁ zero ∷ ones

-- postulate
--   f     : D → D
--   f-eq₁ : ∀ n → f (succ₁ n) ≡ succ₁ zero ∷ f n
--   f-eq₂ : f zero ≡ zero ∷ []

-- ------------------------------------------------------------------------------
-- -- Auxiliary properties

-- fCong : ∀ {m n} → m ≡ n → f m ≡ f n
-- fCong refl = refl

-- succ-∞-Conat : Conat (succ₁ ∞)
-- succ-∞-Conat = subst Conat ∞-eq ∞-Conat

-- ones-Stream : Stream ones
-- ones-Stream = Stream-coind A h refl
--   where
--   A : D → Set
--   A xs = xs ≡ xs

--   h : A ones → ∃[ x' ] ∃[ xs' ] ones ≡ x' ∷ xs' ∧ A xs'
--   h _ = succ₁ zero , ones , ones-eq , refl

-- f-∞-Stream : Stream (f ∞)
-- f-∞-Stream = Stream-coind A h refl
--   where
--   A : D → Set
--   A xs = f xs ≡ f xs

--   h : A (f ∞) → ∃[ x' ] ∃[ xs' ] f ∞ ≡ x' ∷ xs' ∧ A xs'
--   h Af∞ = succ₁ zero , f ∞ , trans (fCong ∞-eq) (f-eq₁ ∞) , Af∞

-- ------------------------------------------------------------------------------
-- -- A proof of (1) adding the N totality hypothesis.

-- thm₁ : ∀ {n} → N n → f n ≢ ones
-- thm₁ nzero h = 0≢S (∧-proj₁ (∷-injective helper))
--   where
--   helper : zero ∷ [] ≡ succ₁ zero ∷ ones
--   helper = trans₂ (sym f-eq₂) h ones-eq

-- thm₁ (nsucc {n} Nn) h = thm₁ Nn (∧-proj₂ (∷-injective helper))
--   where
--   helper : succ₁ zero ∷ f n ≡ succ₁ zero ∷ ones
--   helper = trans₂ (sym (f-eq₁ n)) h ones-eq

-- ------------------------------------------------------------------------------
-- -- A proof of (1) adding the N totality hypothesis and replacing the
-- -- propositional equality by the bisimilarity relation.

-- thm₂ : ∀ {n} → N n → f n ≉ ones
-- thm₂ nzero h with ≈-out h
-- ... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = 0≢S (trans (sym x'≡0) x'≡1)
--   where
--   x'≡0 : x' ≡ zero
--   x'≡0 = ∧-proj₁ (∷-injective (trans (sym prf₁) f-eq₂))

--   x'≡1 : x' ≡ succ₁ zero
--   x'≡1 = ∧-proj₁ (∷-injective (trans (sym prf₂) ones-eq))

-- thm₂ (nsucc {n} Nn) h with ≈-out h
-- ... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = thm₂ Nn (∷-injective≈ helper)
--   where
--   xs'≡fn : xs' ≡ f n
--   xs'≡fn = ∧-proj₂ (∷-injective (trans (sym prf₁) (f-eq₁ n)))

--   ys'≡ones : ys' ≡ ones
--   ys'≡ones = ∧-proj₂ (∷-injective (trans (sym prf₂) ones-eq))

--   helper : x' ∷ f n ≈ x' ∷ ones
--   helper = ≈-in ( x'
--                 , xs'
--                 , ys'
--                 , ∷-rightCong (sym xs'≡fn)
--                 , ∷-rightCong (sym ys'≡ones)
--                 , prf₃
--                 )

-- ------------------------------------------------------------------------------
-- -- A proof of the negation of (1) adding the Conat totality hypothesis
-- -- and replacing the propositional equality by the bisimilarity
-- -- relation.

-- thm₃ : ∃[ n ] (Conat n ∧ f n ≈ ones)
-- thm₃ =  ∞ , ∞-Conat , ≈-coind B h (refl , refl)
--   where
--   B : D → D → Set
--   B xs ys = xs ≡ xs ∧ ys ≡ ys

--   h : B (f ∞) ones →
--       ∃[ x' ] ∃[ xs' ] ∃[ ys' ] f ∞ ≡ x' ∷ xs' ∧ ones ≡ x' ∷ ys' ∧ B xs' ys'
--   h Bh' = succ₁ zero , f ∞ , ones , trans (fCong ∞-eq) (f-eq₁ ∞) , ones-eq , Bh'

------------------------------------------------------------------------------
-- References
--
-- Vytiniotis, D., Peyton Jones, S., Rosén, D. and Claessen,
-- K. (2013). HALO: Haskell to Logic thorugh Denotational
-- Semantics. In: Proceedings of the 40th annual ACM SIGPLAN-SIGACT
-- symposium on Principles of programming languages (POPL’13),
-- pp. 431–442.
