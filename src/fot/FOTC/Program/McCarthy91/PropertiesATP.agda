------------------------------------------------------------------------------
-- Main properties of the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The main properties proved of the McCarthy 91 function (called
-- f₉₁) are

-- 1. The function always terminates.
-- 2. For all n, n < f₉₁ n + 11.
-- 3. For all n > 100, then f₉₁ n = n - 10.
-- 4. For all n <= 100, then f₉₁ n = 91.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesATP
  using ( x>y→x≤y→⊥ )
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( x>y∨x≯y
        ; x≯y→x≤y
        ; x≯Sy→x≯y∨x≡Sy
        ; x+k<y+k→x<y
        ; <-trans
        )
open import FOTC.Data.Nat.PropertiesATP
  using ( ∸-N
        ; +-N
        )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
  using ( x<x+11 )
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
  using ( 10-N
        ; 11-N
        ; 89-N
        ; 90-N
        ; 91-N
        ; 92-N
        ; 93-N
        ; 94-N
        ; 95-N
        ; 96-N
        ; 97-N
        ; 98-N
        ; 99-N
        ; 100-N
        )
open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.AuxiliaryPropertiesATP
open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.WF-Relation
open import FOTC.Program.McCarthy91.WF-Relation.LT2WF-RelationATP
open import FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF-ATP

------------------------------------------------------------------------------
-- For all n > 100, then f₉₁ n = n - 10.
postulate f₉₁-x>100 : ∀ n → n > 100' → f₉₁ n ≡ n ∸ 10'
{-# ATP prove f₉₁-x>100 #-}

-- For all n <= 100, then f₉₁ n = 91.
f₉₁-x≯100 : ∀ {n} → N n → n ≯ 100' → f₉₁ n ≡ 91'
f₉₁-x≯100 = ◁-wfind A h
  where
  A : D → Set
  A d = d ≯ 100' → f₉₁ d ≡ 91'

  h : ∀ {m} → N m → (∀ {k} → N k → k ◁ m → A k) → A m
  h {m} Nm f with x>y∨x≯y Nm 100-N
  ... | inj₁ m>100 = λ m≯100 →
                     ⊥-elim (x>y→x≤y→⊥ Nm 100-N m>100 (x≯y→x≤y Nm 100-N m≯100))
  ... | inj₂ m≯100 with x≯Sy→x≯y∨x≡Sy Nm 99-N m≯100
  ... | inj₂ m≡100 = λ _ → f₉₁-x≡y f₉₁-100 m≡100
  ... | inj₁ m≯99 with x≯Sy→x≯y∨x≡Sy Nm 98-N m≯99
  ... | inj₂ m≡99 = λ _ → f₉₁-x≡y f₉₁-99 m≡99
  ... | inj₁ m≯98 with x≯Sy→x≯y∨x≡Sy Nm 97-N m≯98
  ... | inj₂ m≡98 = λ _ → f₉₁-x≡y f₉₁-98 m≡98
  ... | inj₁ m≯97 with x≯Sy→x≯y∨x≡Sy Nm 96-N m≯97
  ... | inj₂ m≡97 = λ _ → f₉₁-x≡y f₉₁-97 m≡97
  ... | inj₁ m≯96 with x≯Sy→x≯y∨x≡Sy Nm 95-N m≯96
  ... | inj₂ m≡96 = λ _ → f₉₁-x≡y f₉₁-96 m≡96
  ... | inj₁ m≯95 with x≯Sy→x≯y∨x≡Sy Nm 94-N m≯95
  ... | inj₂ m≡95 = λ _ → f₉₁-x≡y f₉₁-95 m≡95
  ... | inj₁ m≯94 with x≯Sy→x≯y∨x≡Sy Nm 93-N m≯94
  ... | inj₂ m≡94 = λ _ → f₉₁-x≡y f₉₁-94 m≡94
  ... | inj₁ m≯93 with x≯Sy→x≯y∨x≡Sy Nm 92-N m≯93
  ... | inj₂ m≡93 = λ _ → f₉₁-x≡y f₉₁-93 m≡93
  ... | inj₁ m≯92 with x≯Sy→x≯y∨x≡Sy Nm 91-N m≯92
  ... | inj₂ m≡92 = λ _ → f₉₁-x≡y f₉₁-92 m≡92
  ... | inj₁ m≯91 with x≯Sy→x≯y∨x≡Sy Nm 90-N m≯91
  ... | inj₂ m≡91 = λ _ → f₉₁-x≡y f₉₁-91 m≡91
  ... | inj₁ m≯90 with x≯Sy→x≯y∨x≡Sy Nm 89-N m≯90
  ... | inj₂ m≡90 = λ _ → f₉₁-x≡y f₉₁-90 m≡90
  ... | inj₁ m≯89 = λ _ → f₉₁-m≯89
    where
    m≤89 : m ≤ 89'
    m≤89 = x≯y→x≤y Nm 89-N m≯89

    f₉₁-m+11 : m + 11' ≯ 100' → f₉₁ (m + 11') ≡ 91'
    f₉₁-m+11 = f (x+11-N Nm) (<→◁ (x+11-N Nm) Nm m≯100 (x<x+11 Nm))

    f₉₁-m≯89 : f₉₁ m ≡ 91'
    f₉₁-m≯89 = f₉₁-x≯100-helper m 91' m≯100
                                (f₉₁-m+11 (x≤89→x+11≯100 Nm m≤89))
                                f₉₁-91

-- The function always terminates.
f₉₁-N : ∀ {n} → N n → N (f₉₁ n)
f₉₁-N {n} Nn = case prf₁ prf₂ (x>y∨x≯y Nn 100-N)
  where
  prf₁ : n > 100' → N (f₉₁ n)
  prf₁ n>100 = subst N (sym (f₉₁-x>100 n n>100)) (∸-N Nn 10-N)

  prf₂ : n ≯ 100' → N (f₉₁ n)
  prf₂ n≯100 = subst N (sym (f₉₁-x≯100 Nn n≯100)) 91-N

-- The function always terminates (using Agda with constructor).
f₉₁-N' : ∀ {n} → N n → N (f₉₁ n)
f₉₁-N' {n} Nn with x>y∨x≯y Nn 100-N
... | inj₁ n>100 = subst N (sym (f₉₁-x>100 n n>100)) (∸-N Nn 10-N)
... | inj₂ n≯100 = subst N (sym (f₉₁-x≯100 Nn n≯100)) 91-N

-- For all n, n < f₉₁ n + 11.
f₉₁-ineq : ∀ {n} → N n → n < f₉₁ n + 11'
f₉₁-ineq = ◁-wfind A h
  where
  A : D → Set
  A d = d < f₉₁ d + 11'

  h : ∀ {m} → N m → (∀ {k} → N k → k ◁ m → A k) → A m
  h {m} Nm f with x>y∨x≯y Nm 100-N
  ... | inj₁ m>100 = x>100→x<f₉₁-x+11 Nm m>100
  ... | inj₂ m≯100 =
    let f₉₁-m+11-N : N (f₉₁ (m + 11'))
        f₉₁-m+11-N = f₉₁-N (+-N Nm 11-N)

        h₁ : A (m + 11')
        h₁ = f (x+11-N Nm) (<→◁ (x+11-N Nm) Nm m≯100 (x<x+11 Nm))

        m<f₉₁m+11 : m < f₉₁ (m + 11')
        m<f₉₁m+11 = x+k<y+k→x<y Nm f₉₁-m+11-N 11-N h₁

        h₂ : A (f₉₁ (m + 11'))
        h₂ = f f₉₁-m+11-N (<→◁ f₉₁-m+11-N Nm m≯100 m<f₉₁m+11)

    in (<-trans Nm f₉₁-m+11-N (x+11-N (f₉₁-N Nm))
                m<f₉₁m+11
                (f₉₁x+11<f₉₁x+11 m m≯100 h₂))
