{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT 20 March 2012.

module Draft.FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Nat

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} h = ≈N-gfp₂ P helper₁ helper₂
  where
  P : D → D → Set
  P a b = Conat a ∧ Conat b ∧ a ≡ b

  helper₁ : ∀ {a b} → P a b → a ≡ zero ∧ b ≡ zero
            ∨ (∃ (λ a' → ∃ (λ b' → P a' b' ∧ a ≡ succ₁ a' ∧ b ≡ succ₁ b')))
  helper₁ {a} {.a} (Ca , Cb , refl) with Conat-gfp₁ Ca
  ... | inj₁ prf = inj₁ (prf , prf)
  ... | inj₂ (a' , Ca' , prf) = inj₂ (a' , a' , (Ca' , Ca' , refl) , (prf , prf))

  helper₂ : Conat n ∧ Conat n ∧ n ≡ n
  helper₂ = h , h , refl

≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈N h₁ h₂ refl = ≈N-refl h₁

{-# NO_TERMINATION_CHECK #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-gfp₁ Cn
... | inj₁ prf = subst N (sym prf) zN
... | inj₂ (n' , Cn' , prf) = subst N (sym prf) (sN {!Conat→N Cn'!})
-- Agda error: Failed to give (Conat→N Cn')

-- TODO: 2012-03-20. Agda bug?
-- N→Conat : ∀ {n} → N n → Conat n
-- N→Conat zN          = Conat-gfp₃ (inj₁ refl)
-- N→Conat (sN {n} Nn) = Conat-gfp₃ (inj₂ (n , ({!N→Conat Nn!} , refl)))
-- Agda error: Failed to give N→Conat Nn

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-gfp₂ N helper Nn
  where
  helper : ∀ {m} → N m → m ≡ zero ∨ ∃ (λ m' → N m' ∧ m ≡ succ₁ m')
  helper zN          = inj₁ refl
  helper (sN {m} Nm) = inj₂ (m , Nm , refl)
