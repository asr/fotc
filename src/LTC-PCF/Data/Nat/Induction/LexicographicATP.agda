------------------------------------------------------------------------------
-- Well-founded induction on the lexicographic order the natural numbers
------------------------------------------------------------------------------

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC-PCF.Data.Nat.Induction.LexicographicATP where

open import LTC-PCF.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The LTC natural numbers type.
        )

open import LTC-PCF.Data.Nat.Inequalities using ( LT ; LT₂ )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
  using ( 0<0→⊥
        ; 0Sx<00→⊥
        ; Sxy₁<0y₂→⊥
        ; x<0→⊥
        ; xy<00→⊥
        ; ≤-trans
        ; Sx≤y→x<y
        ; Sx≤Sy→x≤y
        ; x<Sy→x<y∨x≡y
        ; x<y→Sx≤y
        ; x<y→x<Sy
        ; x<y→y≡z→x<z
        ; x≡y→y<z→x<z
        ; x₁y<x₂0→x₁<x₂
        )

------------------------------------------------------------------------------

wfInd-LT₂ :
  (P : D → D → Set) →
  (∀ {m₁ n₁} → N m₁ → N n₁ →
     (∀ {m₂ n₂} → N m₂ → N n₂ → LT₂ m₂ n₂ m₁ n₁ → P m₂ n₂) → P m₁ n₁) →
  ∀ {m n} → N m → N n → P m n
wfInd-LT₂ P accH Nm Nn = accH Nm Nn (helper₂ Nm Nn)
  where
    helper₁ : ∀ {m n o} → N m → N n → N o → LT m o → LT o (succ n) → LT m n
    helper₁ {m} {n} {o} Nm Nn No m<o o<Sn =
      Sx≤y→x<y Nm Nn (≤-trans (sN Nm) No Nn
                              (x<y→Sx≤y Nm No m<o)
                              (Sx≤Sy→x≤y {o} {n} (x<y→Sx≤y No (sN Nn) o<Sn)))

    helper₂ : ∀ {m₁ n₁ m₂ n₂} → N m₁ → N n₁ → N m₂ → N n₂ →
              LT₂ m₂ n₂ m₁ n₁ → P m₂ n₂

    helper₂ Nm₁ Nn₂ zN zN 00<00 =
      accH zN zN (λ Nm' Nn' m'n'<00 → ⊥-elim $ xy<00→⊥ Nm' Nn' m'n'<00)

    helper₂ zN zN (sN Nm₂) zN Sm₂0<00 = ⊥-elim $ Sxy₁<0y₂→⊥ Nm₂ zN zN Sm₂0<00

    helper₂ (sN Nm₁) zN (sN Nm₂) zN Sm₂0<Sm₁0 =
      accH (sN Nm₂) zN (λ Nm' Nn' m'n'<Sm₂0 →
        helper₂ Nm₁ zN Nm' Nn'
                (inj₁ (helper₁ Nm' Nm₁ (sN Nm₂)
                               (x₁y<x₂0→x₁<x₂ Nm' Nn' (sN Nm₂) m'n'<Sm₂0)
                               (x₁y<x₂0→x₁<x₂ (sN Nm₂) zN (sN Nm₁) Sm₂0<Sm₁0))))

    helper₂ zN (sN Nn₁) (sN Nm₂) zN Sm₂0<0Sn₁ =
      ⊥-elim $ Sxy₁<0y₂→⊥ Nm₂ zN (sN Nn₁) Sm₂0<0Sn₁

    helper₂ (sN Nm₁) (sN Nn₁) (sN Nm₂) zN Sm₂0<Sm₁Sn₁ =
      accH (sN Nm₂) zN (λ Nm' Nn' m'n'<Sm₂0 →
        helper₂ (sN Nm₁) Nn₁ Nm' Nn'
          (inj₁ ([ (λ Sm₂<Sm₁ → x<y→x<Sy Nm' Nm₁
                                         (helper₁ Nm' Nm₁ (sN Nm₂)
                                                  (x₁y<x₂0→x₁<x₂ Nm' Nn' (sN Nm₂)
                                                                 m'n'<Sm₂0)
                                                  Sm₂<Sm₁))
                 , (λ Sm₂≡Sm₁∧0<Sn₁ → x<y→y≡z→x<z (x₁y<x₂0→x₁<x₂ Nm' Nn' (sN Nm₂)
                                                                 m'n'<Sm₂0)
                                                  (∧-proj₁ Sm₂≡Sm₁∧0<Sn₁))
                 ]
                Sm₂0<Sm₁Sn₁)))

    helper₂ zN zN zN (sN Nn₂) 0Sn₂<00 = ⊥-elim $ 0Sx<00→⊥ Nn₂ 0Sn₂<00

    helper₂ (sN {m₁} Nm₁) zN zN (sN Nn₂) 0Sn₂<Sm₁0 =
      accH zN (sN Nn₂) (λ Nm' Nn' m'n'<0Nn₂ →
        helper₂ Nm₁ (sN Nn₂) Nm' Nn'
                ([ (λ m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)
                , (λ m'≡0∧n'<Sn₂ →
                     [ (λ 0<m₁ → inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡0∧n'<Sn₂) 0<m₁))
                     , (λ 0≡m₁ →
                          inj₂ ((trans (∧-proj₁ m'≡0∧n'<Sn₂) 0≡m₁)
                               , (∧-proj₂ m'≡0∧n'<Sn₂)))
                     ]
                     (x<Sy→x<y∨x≡y zN Nm₁ 0<Sm₁))
                ]
                m'n'<0Nn₂))

      where
        0<Sm₁ : LT zero (succ m₁)
        0<Sm₁ = x₁y<x₂0→x₁<x₂ zN (sN Nn₂) (sN Nm₁) 0Sn₂<Sm₁0

    helper₂ zN (sN Nn₁) zN (sN Nn₂) 0Sn₂<0Sn₁ =
      [ (λ 0<0 → ⊥-elim $ 0<0→⊥ 0<0)
      , (λ 0≡0∧Sn₂<Sn₁ →
           accH zN (sN Nn₂) (λ Nm' Nn' m'n'<0Sn₂ →
             [ (λ m'<0        → ⊥-elim $ x<0→⊥ Nm' m'<0)
             , (λ m'≡0∧n'<Sn₂ →
                  helper₂ zN Nn₁ Nm' Nn'
                        (inj₂ (∧-proj₁ m'≡0∧n'<Sn₂
                              , helper₁ Nn' Nn₁ (sN Nn₂)
                                        (∧-proj₂ m'≡0∧n'<Sn₂)
                                        (∧-proj₂ 0≡0∧Sn₂<Sn₁))))
             ]
             m'n'<0Sn₂))
      ]
      0Sn₂<0Sn₁

    helper₂ (sN Nm₁) (sN Nn₁) zN (sN Nn₂) 0Sn₂<Sm₁Sn₁ =
      accH zN (sN Nn₂) (λ Nm' Nn' m'n'<0Sn₂ →
        helper₂ (sN Nm₁) Nn₁ Nm' Nn'
          ([ (λ m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)
           , (λ m'≡0∧n'<Sn₂ →
                [ (λ 0<Sm₁ → inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡0∧n'<Sn₂) 0<Sm₁))
                , (λ 0≡Sn₂∧Sn₂<Sn₁ → ⊥-elim $ 0≠S $ ∧-proj₁ 0≡Sn₂∧Sn₂<Sn₁)
                ] 0Sn₂<Sm₁Sn₁)
           ]
           m'n'<0Sn₂))

    helper₂ zN zN (sN Nm₂) (sN Nn₂) Sm₂Sn₂<00 =
      ⊥-elim $ xy<00→⊥ (sN Nm₂) (sN Nn₂) Sm₂Sn₂<00

    helper₂ (sN {m₁} Nm₁) zN (sN {m₂} Nm₂) (sN Nn₂) Sm₂Sn₂<Sm₁0 =
      accH (sN Nm₂) (sN Nn₂) (λ Nm' Nn' m'n'<Sm₂Sn₂ →
        helper₂ Nm₁ (sN Nn₂) Nm' Nn'
          ([ (λ m'<Sm₂ →
                inj₁ (helper₁ Nm' Nm₁ (sN Nm₂) m'<Sm₂ Sm₂<Sm₁))
          , (λ m'≡Sm₂∧n'<Sn₂ →
               [ (λ m'<m₁ → inj₁ m'<m₁)
                 , (λ m'≡m₁ → inj₂ (m'≡m₁ , ∧-proj₂ m'≡Sm₂∧n'<Sn₂))
               ]
               (x<Sy→x<y∨x≡y Nm' Nm₁
                             (x≡y→y<z→x<z (∧-proj₁ m'≡Sm₂∧n'<Sn₂) Sm₂<Sm₁)))
          ] m'n'<Sm₂Sn₂))

        where
          Sm₂<Sm₁ : LT (succ m₂) (succ m₁)
          Sm₂<Sm₁ = x₁y<x₂0→x₁<x₂ (sN Nm₂) (sN Nn₂) (sN Nm₁) Sm₂Sn₂<Sm₁0

    helper₂ zN (sN Nn₁) (sN Nm₂) (sN Nn₂) Sm₂Sn₂<0Sn₁
      = ⊥-elim $ Sxy₁<0y₂→⊥ Nm₂ (sN Nn₂) (sN Nn₁) Sm₂Sn₂<0Sn₁

    helper₂ (sN Nm₁) (sN Nn₁) (sN Nm₂) (sN Nn₂) Sm₂Sn₂<Sm₁Sn₁ =
      accH (sN Nm₂) (sN Nn₂) (λ Nm' Nn' m'n'<Sm₂Sn₂ →
        helper₂ (sN Nm₁) Nn₁ Nm' Nn'
          ([ (λ Sm₂<Sm₁ →
                [ (λ m'<Sm₂ → inj₁ (x<y→x<Sy Nm' Nm₁
                                             (helper₁ Nm' Nm₁ (sN Nm₂)
                                                      m'<Sm₂
                                                      Sm₂<Sm₁)))

                , (λ m'≡Sm₂∧n'<Sn₂ →
                     inj₁ (x≡y→y<z→x<z (∧-proj₁ m'≡Sm₂∧n'<Sn₂) Sm₂<Sm₁))
                ]
                m'n'<Sm₂Sn₂)

          , (λ Sm₂≡Sm₁∧Sn₂<Sn₁ →
               [ (λ m'<Sm₂ →
                    inj₁ (x<y→y≡z→x<z m'<Sm₂ (∧-proj₁ Sm₂≡Sm₁∧Sn₂<Sn₁)))
               , (λ m'≡Sm₂∧n'<Sn₂ → inj₂
                    ( trans (∧-proj₁ m'≡Sm₂∧n'<Sn₂) (∧-proj₁ Sm₂≡Sm₁∧Sn₂<Sn₁)
                    , helper₁ Nn' Nn₁ (sN Nn₂)
                              (∧-proj₂ m'≡Sm₂∧n'<Sn₂)
                              (∧-proj₂ Sm₂≡Sm₁∧Sn₂<Sn₁)
                    )
                 )
               ]
               m'n'<Sm₂Sn₂)
          ]
          Sm₂Sn₂<Sm₁Sn₁))
