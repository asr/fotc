------------------------------------------------------------------------------
-- Well-founded induction on the lexicographic order on natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Nat.Induction.NonAcc.LexicographicI where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesI
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

Lexi-wfind :
  (A : D → D → Set) →
  (∀ {m₁ n₁} → N m₁ → N n₁ →
     (∀ {m₂ n₂} → N m₂ → N n₂ → Lexi m₂ n₂ m₁ n₁ → A m₂ n₂) → A m₁ n₁) →
  ∀ {m n} → N m → N n → A m n
Lexi-wfind A h Nm Nn = h Nm Nn (helper₂ Nm Nn)
  where
  helper₁ : ∀ {m n o} → N m → N n → N o → m < o → o < succ₁ n  → m < n
  helper₁ {m} {n} {o} Nm Nn No m<o o<Sn =
    Sx≤y→x<y Nm Nn (≤-trans (nsucc Nm) No Nn
                            (x<y→Sx≤y Nm No m<o)
                            (Sx≤Sy→x≤y {o} {n} (x<y→Sx≤y No (nsucc Nn) o<Sn)))

  helper₂ : ∀ {m₁ n₁ m₂ n₂} → N m₁ → N n₁ → N m₂ → N n₂ →
            Lexi m₂ n₂ m₁ n₁ → A m₂ n₂

  helper₂ Nm₁ Nn₂ nzero nzero 00<00 =
    h nzero nzero (λ Nm' Nn' m'n'<00 → ⊥-elim (xy<00→⊥ Nm' Nn' m'n'<00))

  helper₂ nzero nzero (nsucc Nm₂) nzero Sm₂0<00 = ⊥-elim (Sxy<0y'→⊥ Sm₂0<00)

  helper₂ (nsucc Nm₁) nzero (nsucc Nm₂) nzero Sm₂0<Sm₁0 =
    h (nsucc Nm₂) nzero (λ Nm' Nn' m'n'<Sm₂0 →
      helper₂ Nm₁ nzero Nm' Nn'
              (inj₁ (helper₁ Nm' Nm₁ (nsucc Nm₂)
                             (xy<x'0→x<x' Nn' m'n'<Sm₂0)
                             (xy<x'0→x<x' nzero Sm₂0<Sm₁0))))

  helper₂ nzero (nsucc Nn₁) (nsucc Nm₂) nzero Sm₂0<0Sn₁ =
    ⊥-elim (Sxy<0y'→⊥ Sm₂0<0Sn₁)

  helper₂ (nsucc Nm₁) (nsucc Nn₁) (nsucc Nm₂) nzero Sm₂0<Sm₁Sn₁ =
    h (nsucc Nm₂) nzero (λ Nm' Nn' m'n'<Sm₂0 →
      helper₂ (nsucc Nm₁) Nn₁ Nm' Nn'
        (inj₁ (case (λ Sm₂<Sm₁ → x<y→x<Sy Nm' Nm₁
                                          (helper₁ Nm' Nm₁ (nsucc Nm₂)
                                                  (xy<x'0→x<x' Nn' m'n'<Sm₂0)
                                                  Sm₂<Sm₁))
                    (λ Sm₂≡Sm₁∧0<Sn₁ → x<y→y≡z→x<z (xy<x'0→x<x' Nn' m'n'<Sm₂0)
                                                   (∧-proj₁ Sm₂≡Sm₁∧0<Sn₁))
                    Sm₂0<Sm₁Sn₁)))

  helper₂ nzero nzero nzero (nsucc Nn₂) 0Sn₂<00 = ⊥-elim (0Sx<00→⊥ 0Sn₂<00)

  helper₂ (nsucc {m₁} Nm₁) nzero nzero (nsucc Nn₂) 0Sn₂<Sm₁0 =
    h nzero (nsucc Nn₂) (λ Nm' Nn' m'n'<0Nn₂ →
      helper₂ Nm₁ (nsucc Nn₂) Nm' Nn'
              (case (λ m'<0 → ⊥-elim (x<0→⊥ Nm' m'<0))
                    (λ m'≡0∧n'<Sn₂ →
                      case (λ 0<m₁ → inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡0∧n'<Sn₂) 0<m₁))
                           (λ 0≡m₁ → inj₂ ((trans (∧-proj₁ m'≡0∧n'<Sn₂) 0≡m₁)
                                          , (∧-proj₂ m'≡0∧n'<Sn₂)))
                           (x<Sy→x<y∨x≡y nzero Nm₁ 0<Sm₁))
                    m'n'<0Nn₂))

    where
    0<Sm₁ : zero < succ₁ m₁
    0<Sm₁ = xy<x'0→x<x' (nsucc Nn₂) 0Sn₂<Sm₁0

  helper₂ nzero (nsucc Nn₁) nzero (nsucc Nn₂) 0Sn₂<0Sn₁ =
    case (λ 0<0 → ⊥-elim (0<0→⊥ 0<0))
         (λ 0≡0∧Sn₂<Sn₁ →
           h nzero (nsucc Nn₂) (λ Nm' Nn' m'n'<0Sn₂ →
             case (λ m'<0 → ⊥-elim (x<0→⊥ Nm' m'<0))
                  (λ m'≡0∧n'<Sn₂ →
                    helper₂ nzero Nn₁ Nm' Nn'
                      (inj₂ (∧-proj₁ m'≡0∧n'<Sn₂
                            , helper₁ Nn' Nn₁ (nsucc Nn₂)
                                          (∧-proj₂ m'≡0∧n'<Sn₂)
                                          (∧-proj₂ 0≡0∧Sn₂<Sn₁))))
                  m'n'<0Sn₂))
         0Sn₂<0Sn₁

  helper₂ (nsucc Nm₁) (nsucc Nn₁) nzero (nsucc Nn₂) 0Sn₂<Sm₁Sn₁ =
    h nzero (nsucc Nn₂) (λ Nm' Nn' m'n'<0Sn₂ →
      helper₂ (nsucc Nm₁) Nn₁ Nm' Nn'
        (case (λ m'<0 → ⊥-elim (x<0→⊥ Nm' m'<0))
              (λ m'≡0∧n'<Sn₂ →
                case (λ 0<Sm₁ → inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡0∧n'<Sn₂) 0<Sm₁))
                     (λ 0≡Sn₂∧Sn₂<Sn₁ → ⊥-elim (0≢S (∧-proj₁ 0≡Sn₂∧Sn₂<Sn₁)))
                     0Sn₂<Sm₁Sn₁)
              m'n'<0Sn₂))

  helper₂ nzero nzero (nsucc Nm₂) (nsucc Nn₂) Sm₂Sn₂<00 =
    ⊥-elim (xy<00→⊥ (nsucc Nm₂) (nsucc Nn₂) Sm₂Sn₂<00)

  helper₂ (nsucc {m₁} Nm₁) nzero (nsucc {m₂} Nm₂) (nsucc Nn₂) Sm₂Sn₂<Sm₁0 =
    h (nsucc Nm₂) (nsucc Nn₂) (λ Nm' Nn' m'n'<Sm₂Sn₂ →
      helper₂ Nm₁ (nsucc Nn₂) Nm' Nn'
        (case (λ m'<Sm₂ → inj₁ (helper₁ Nm' Nm₁ (nsucc Nm₂) m'<Sm₂ Sm₂<Sm₁))
              (λ m'≡Sm₂∧n'<Sn₂ →
                case (λ m'<m₁ → inj₁ m'<m₁)
                     (λ m'≡m₁ → inj₂ (m'≡m₁ , ∧-proj₂ m'≡Sm₂∧n'<Sn₂))
                     (x<Sy→x<y∨x≡y Nm' Nm₁
                                   (x≡y→y<z→x<z (∧-proj₁ m'≡Sm₂∧n'<Sn₂) Sm₂<Sm₁)))
              m'n'<Sm₂Sn₂))

    where
    Sm₂<Sm₁ : succ₁ m₂ < succ₁ m₁
    Sm₂<Sm₁ = xy<x'0→x<x' (nsucc Nn₂) Sm₂Sn₂<Sm₁0

  helper₂ nzero (nsucc Nn₁) (nsucc Nm₂) (nsucc Nn₂) Sm₂Sn₂<0Sn₁
    = ⊥-elim (Sxy<0y'→⊥ Sm₂Sn₂<0Sn₁)

  helper₂ (nsucc Nm₁) (nsucc Nn₁) (nsucc Nm₂) (nsucc Nn₂) Sm₂Sn₂<Sm₁Sn₁ =
    h (nsucc Nm₂) (nsucc Nn₂) (λ Nm' Nn' m'n'<Sm₂Sn₂ →
      helper₂ (nsucc Nm₁) Nn₁ Nm' Nn'
        (case (λ Sm₂<Sm₁ →
                 case (λ m'<Sm₂ → inj₁ (x<y→x<Sy Nm' Nm₁ (helper₁ Nm' Nm₁ (nsucc Nm₂) m'<Sm₂ Sm₂<Sm₁)))
                      (λ m'≡Sm₂∧n'<Sn₂ → inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡Sm₂∧n'<Sn₂) Sm₂<Sm₁))
                      m'n'<Sm₂Sn₂)

              (λ Sm₂≡Sm₁∧Sn₂<Sn₁ →
                case (λ m'<Sm₂ → inj₁ (x<y→y≡z→x<z m'<Sm₂ (∧-proj₁ Sm₂≡Sm₁∧Sn₂<Sn₁)))
                     (λ m'≡Sm₂∧n'<Sn₂ → inj₂
                       (trans (∧-proj₁ m'≡Sm₂∧n'<Sn₂) (∧-proj₁ Sm₂≡Sm₁∧Sn₂<Sn₁)
                       , helper₁ Nn' Nn₁ (nsucc Nn₂) (∧-proj₂ m'≡Sm₂∧n'<Sn₂) (∧-proj₂ Sm₂≡Sm₁∧Sn₂<Sn₁)))
                     m'n'<Sm₂Sn₂)
              Sm₂Sn₂<Sm₁Sn₁))
