------------------------------------------------------------------------------
-- Equality on conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.Equality where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infix 7 _≈N_

------------------------------------------------------------------------------
-- The equality on Conat.
postulate
  _≈N_ : D → D → Set

-- The relation _≈N_ is the greatest post-fixed point of the
-- functional ≈NF (by ≈N-gfp₁ and ≈N-gfp₂).

-- The equality on Conat functional.
-- Adapted from Herbert's thesis, p. 58.
-- ≈NF : (D → D → Set) → D → D → Set
-- ≈NF _R_ m n = ∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ m' ∧ n ≡ succ n'

-- The relation _≈N_ is a post-fixed point of the functional ≈NF.
postulate
  ≈N-gfp₁ : ∀ {m n} → m ≈N n →
            ∃[ m' ] ∃[ n' ] m' ≈N n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n'
{-# ATP axiom ≈N-gfp₁ #-}

-- N.B. This is a second-order axiom. In the automatic proofs, we
-- *must* use an instance. Therefore, we do not add this postulate as
-- an ATP axiom.
postulate
  ≈N-gfp₂ : (_R_ : D → D → Set) →
            -- R is a post-fixed point of the functional ≈NF.
           (∀ {m n} → m R n →
            ∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n') →
           -- _≈N_ is greater than R.
           ∀ {m n} → m R n → m ≈N n

-- Because a greatest post-fixed point is a fixed point, the relation
-- _≈N_ is also a pre-fixed point of functional ≈NF.
≈N-gfp₃ : ∀ {m n} →
          (∃[ m' ] ∃[ n' ] m' ≈N n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n') →
          m ≈N n
≈N-gfp₃ h = ≈N-gfp₂ _R_ helper h
  where
  _R_ : D → D → Set
  _R_ m n = ∃[ m' ] ∃[ n' ] m' ≈N n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n'

  helper : ∀ {m n} → m R n →
           ∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n'
  helper (∃-intro (∃-intro (m'≈Nn' , prf))) =
    ∃-intro (∃-intro (≈N-gfp₁ m'≈Nn' , prf))
