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

Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-unf cozero          = inj₁ refl
Conat-unf (cosucc {n} Cn) = inj₂ (n , refl , ♭ Cn)

Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
           Conat n
Conat-in (inj₁ n≡0)              = subst Conat (sym n≡0) cozero
Conat-in (inj₂ (n' , prf , Cn')) = subst Conat (sym prf) (cosucc (♯ Cn'))

Conat-coind : (A : D → Set) →
              (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
              ∀ {n} → A n → Conat n
Conat-coind A h {n} An = Conat-in (case prf₁ prf₂ (h An))
  where
  prf₁ : n ≡ zero → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₁ n≡0 = inj₁ n≡0

  prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ A n'  →
         n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₂ (n' , prf , An') = inj₂ (n' , prf , {!!})

postulate
  inf    : D
  inf-eq : inf ≡ succ₁ inf
{-# ATP axiom inf-eq #-}

{-# NO_TERMINATION_CHECK #-}
inf-Conat : Conat inf
inf-Conat = subst Conat (sym inf-eq) (cosucc (♯ inf-Conat))
