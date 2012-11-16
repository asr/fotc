------------------------------------------------------------------------------
-- Main properties of the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The main properties proved of the McCarthy 91 function (called
-- mc91) are

-- 1. The function always terminates.
-- 2. For all n, n < mc91 n + 11.
-- 3. For all n > 100, then mc91 n = n - 10.
-- 4. For all n <= 100, then mc91 n = 91.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.AuxiliaryPropertiesATP
open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.WF-Relation
open import FOTC.Program.McCarthy91.WF-Relation.LT2WF-RelationATP
open import FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF-ATP

------------------------------------------------------------------------------
-- For all n > 100, then mc91 n = n - 10.
postulate mc91-res>100 : ∀ n → n > [100] → mc91 n ≡ n ∸ [10]
{-# ATP prove mc91-res>100 #-}

-- For all n <= 100, then mc91 n = 91.
mc91-res≯100 : ∀ {n} → N n → n ≯ [100] → mc91 n ≡ [91]
mc91-res≯100 = ≪-wfind A h
  where
  A : D → Set
  A d = d ≯ [100] → mc91 d ≡ [91]

  h : ∀ {m} → N m → (∀ {k} → N k → k ≪ m → A k) → A m
  h {m} Nm f with x>y∨x≯y Nm 100-N
  ... | inj₁ m>100 = λ m≯100 →
                     ⊥-elim (x>y→x≤y→⊥ Nm 100-N m>100 (x≯y→x≤y Nm 100-N m≯100))
  ... | inj₂ m≯100 with x≯Sy→x≯y∨x≡Sy Nm 99-N m≯100
  ... | inj₂ m≡100 = λ _ → mc91-res-aux mc91-res-100 m≡100
  ... | inj₁ m≯99 with x≯Sy→x≯y∨x≡Sy Nm 98-N m≯99
  ... | inj₂ m≡99 = λ _ → mc91-res-aux mc91-res-99 m≡99
  ... | inj₁ m≯98 with x≯Sy→x≯y∨x≡Sy Nm 97-N m≯98
  ... | inj₂ m≡98 = λ _ → mc91-res-aux mc91-res-98 m≡98
  ... | inj₁ m≯97 with x≯Sy→x≯y∨x≡Sy Nm 96-N m≯97
  ... | inj₂ m≡97 = λ _ → mc91-res-aux mc91-res-97 m≡97
  ... | inj₁ m≯96 with x≯Sy→x≯y∨x≡Sy Nm 95-N m≯96
  ... | inj₂ m≡96 = λ _ → mc91-res-aux mc91-res-96 m≡96
  ... | inj₁ m≯95 with x≯Sy→x≯y∨x≡Sy Nm 94-N m≯95
  ... | inj₂ m≡95 = λ _ → mc91-res-aux mc91-res-95 m≡95
  ... | inj₁ m≯94 with x≯Sy→x≯y∨x≡Sy Nm 93-N m≯94
  ... | inj₂ m≡94 = λ _ → mc91-res-aux mc91-res-94 m≡94
  ... | inj₁ m≯93 with x≯Sy→x≯y∨x≡Sy Nm 92-N m≯93
  ... | inj₂ m≡93 = λ _ → mc91-res-aux mc91-res-93 m≡93
  ... | inj₁ m≯92 with x≯Sy→x≯y∨x≡Sy Nm 91-N m≯92
  ... | inj₂ m≡92 = λ _ → mc91-res-aux mc91-res-92 m≡92
  ... | inj₁ m≯91 with x≯Sy→x≯y∨x≡Sy Nm 90-N m≯91
  ... | inj₂ m≡91 = λ _ → mc91-res-aux mc91-res-91 m≡91
  ... | inj₁ m≯90 with x≯Sy→x≯y∨x≡Sy Nm 89-N m≯90
  ... | inj₂ m≡90 = λ _ → mc91-res-aux mc91-res-90 m≡90
  ... | inj₁ m≯89 = λ _ → mc91-res-m≯89
    where
    m≤89 : m ≤ [89]
    m≤89 = x≯y→x≤y Nm 89-N m≯89

    mc91-res-m+11 : m + [11] ≯ [100] → mc91 (m + [11]) ≡ [91]
    mc91-res-m+11 = f (x+11-N Nm) (<→≪ (x+11-N Nm) Nm m≯100 (x<x+11 Nm))

    mc91-res-m≯89 : mc91 m ≡ [91]
    mc91-res-m≯89 = mc91x-res≯100 m [91] m≯100
                                  (mc91-res-m+11 (x≤89→x+11≯100 Nm m≤89))
                                  mc91-res-91
-- The function always terminates.
mc91-N : ∀ {n} → N n → N (mc91 n)
mc91-N {n} Nn with x>y∨x≯y Nn 100-N
... | inj₁ n>100 = subst N (sym (mc91-res>100 n n>100)) (∸-N Nn 10-N)
... | inj₂ n≮100 = subst N (sym (mc91-res≯100 Nn n≮100)) 91-N

-- For all n, n < mc91 n + 11.
mc91-N-ineq : ∀ {n} → N n → n < mc91 n + [11]
mc91-N-ineq = ≪-wfind A h
  where
  A : D → Set
  A d = d < mc91 d + [11]

  h : ∀ {m} → N m → (∀ {k} → N k → k ≪ m → A k) → A m
  h {m} Nm f with x>y∨x≯y Nm 100-N
  ... | inj₁ m>100 = x<mc91x+11>100 Nm m>100
  ... | inj₂ m≯100 =
    let mc91-m+11-N : N (mc91 (m + [11]))
        mc91-m+11-N = mc91-N (+-N Nm 11-N)

        h₁ : A (m + [11])
        h₁ = f (x+11-N Nm) (<→≪ (x+11-N Nm) Nm m≯100 (x<x+11 Nm))

        m<mc91m+11 : m < mc91 (m + [11])
        m<mc91m+11 = x+k<y+k→x<y Nm mc91-m+11-N 11-N h₁

        h₂ : A (mc91 (m + [11]))
        h₂ = f mc91-m+11-N (<→≪ mc91-m+11-N Nm m≯100 m<mc91m+11)

    in (<-trans Nm mc91-m+11-N (x+11-N (mc91-N Nm))
                m<mc91m+11
                (mc91x+11<mc91x+11 m m≯100 h₂))
