------------------------------------------------------------------------------
-- Definition of FOTC Conat using Agda's co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.TypeSL where

open import Coinduction
open import FOTC.Base

------------------------------------------------------------------------------

data Conat : D → Set where
  cozero : Conat zero
  cosucc : ∀ {n} → ∞ (Conat n) → Conat (succ₁ n)

Conat-out : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-out cozero          = inj₁ refl
Conat-out (cosucc {n} Cn) = inj₂ (n , refl , ♭ Cn)

Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
           Conat n
Conat-in (inj₁ n≡0)              = subst Conat (sym n≡0) cozero
Conat-in (inj₂ (n' , prf , Cn')) = subst Conat (sym prf) (cosucc (♯ Cn'))

-- 25 June 2014. Requires the non-termination flag when using
-- --without-K. See Agda issue 1214.
{-# NO_TERMINATION_CHECK #-}
Conat-coind : (A : D → Set) →
              (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
              ∀ {n} → A n → Conat n
Conat-coind A h An with h An
... | inj₁ refl = cozero
... | inj₂ (n' , refl , An') = cosucc (♯ (Conat-coind A h An'))

-- TODO (07 January 2014): We couldn't prove Conat-stronger-coind.
Conat-stronger-coind :
  ∀ (A : D → Set) {n} →
  (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  A n → Conat n
Conat-stronger-coind A h An with h An
... | inj₁ n≡0 = subst Conat (sym n≡0) cozero
... | inj₂ (n' , prf , An') =
  subst Conat (sym prf) (cosucc (♯ (Conat-coind A {!!} An')))

postulate
  ∞D    : D
  ∞-eq : ∞D ≡ succ₁ ∞D

-- TODO (06 January 2014): Agda doesn't accept the proof of Conat ∞D.
{-# NO_TERMINATION_CHECK #-}
∞-Conat : Conat ∞D
∞-Conat = subst Conat (sym ∞-eq) (cosucc (♯ ∞-Conat))
