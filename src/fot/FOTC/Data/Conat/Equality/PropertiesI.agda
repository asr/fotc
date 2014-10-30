------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Conat.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- relation _≈_ is also a pre-fixed point of the functional ≈-F, i.e.
--
-- ≈-F _≈_ ≤ _≈_ (see FOTC.Data.Conat.Equality.Type).
≈-in :
  ∀ {m n} →
  m ≡ zero ∧ n ≡ zero
    ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈ n') →
  m ≈ n
≈-in h = ≈-coind R h' h
  where
  R : D → D → Set
  R m n = m ≡ zero ∧ n ≡ zero
            ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈ n')

  h' : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  h' (inj₁ prf) = inj₁ prf
  h' (inj₂ (m' , n' , prf₁ , prf₂ , m'≈n')) =
    inj₂ (m' , n' , prf₁ , prf₂ , ≈-out m'≈n')

≈-refl : ∀ {n} → Conat n → n ≈ n
≈-refl {n} Cn = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b

  h₁ : ∀ {a b} → R a b →
       a ≡ zero ∧ b ≡ zero
         ∨ (∃[ a' ] ∃[ b' ] a ≡ succ₁ a' ∧ b ≡ succ₁ b' ∧ R a' b')
  h₁ (Ca , Cb , h) with Conat-out Ca
  ... | inj₁ prf              = inj₁ (prf , trans (sym h) prf)
  ... | inj₂ (a' , prf , Ca') =
    inj₂ (a' , a' , prf , trans (sym h) prf , (Ca' , Ca' , refl))

  h₂ : R n n
  h₂ = Cn , Cn , refl

≡→≈ : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈ n
≡→≈ Cm _ refl = ≈-refl Cm
