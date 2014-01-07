------------------------------------------------------------------------------
-- Definition of FOTC Conat using Agda's co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.TypeSL where

open import FOTC.Base
open import Coinduction

------------------------------------------------------------------------------

data Conat : D → Set where
  cozero : Conat zero
  cosucc : ∀ {n} → (∞ (Conat n)) → Conat (succ₁ n)

Conat-out : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-out cozero          = inj₁ refl
Conat-out (cosucc {n} Cn) = inj₂ (n , refl , ♭ Cn)

Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
           Conat n
Conat-in (inj₁ n≡0)              = subst Conat (sym n≡0) cozero
Conat-in (inj₂ (n' , prf , Cn')) = subst Conat (sym prf) (cosucc (♯ Cn'))

-- TODO (06 January 2014). We couldn't prove Conat-coind.
Conat-coind : (A : D → Set) →
              (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
              ∀ {n} → A n → Conat n
Conat-coind A h {n} An = Conat-in (case prf₁ prf₂ (h An))
  where
  prf₁ : n ≡ zero → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₁ n≡0 = inj₁ n≡0

  prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ A n' →
         n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₂ (n' , prf , An') = inj₂ (n' , prf , {!!})

postulate
  ∞D    : D
  ∞-eq : ∞D ≡ succ₁ ∞D

-- TODO (06 January 2014): Agda doesn't accept the proof of Conat ∞.
{-# NO_TERMINATION_CHECK #-}
∞-Conat : Conat ∞D
∞-Conat = subst Conat (sym ∞-eq) (cosucc (♯ ∞-Conat))
