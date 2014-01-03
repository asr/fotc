------------------------------------------------------------------------------
-- Definition of FOTC Conat using Agda's co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.ConatSL where

open import FOTC.Base
open import Coinduction

------------------------------------------------------------------------------

data Conat : D → Set where
  cozero : Conat zero
  cosucc : ∀ {n} → (∞ (Conat n)) → Conat (succ₁ n)

Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n')
Conat-unf cozero          = inj₁ refl
Conat-unf (cosucc {n} Cn) = inj₂ (n , ♭ Cn , refl)

Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n') →
           Conat n
Conat-in (inj₁ h) = subst Conat (sym h) cozero
Conat-in (inj₂ (n , Cn , h)) = subst Conat (sym h) (cosucc (♯ Cn))

Conat-coind : ∀ (A : D → Set) {n} →
              (A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
              A n → Conat n
Conat-coind A h An = {!!}

postulate
  inf    : D
  inf-eq : inf ≡ succ₁ inf
{-# ATP axiom inf-eq #-}

{-# NO_TERMINATION_CHECK #-}
inf-Conat : Conat inf
inf-Conat = subst Conat (sym inf-eq) (cosucc (♯ inf-Conat))
