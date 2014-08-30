------------------------------------------------------------------------------
-- Inductive PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesI where

open import PA.Inductive.Base
open import PA.Inductive.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succCong refl = refl

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong refl = refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong refl = refl

------------------------------------------------------------------------------
-- Peano's third axiom.
P₃ : ∀ {m n} → succ m ≡ succ n → m ≡ n
P₃ refl = refl

-- Peano's fourth axiom.
P₄ : ∀ {n} → zero ≢ succ n
P₄ ()

x≢Sx : ∀ {n} → n ≢ succ n
x≢Sx {zero} ()
x≢Sx {succ n} h = x≢Sx (P₃ h)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

-- Adapted from the Agda standard library 0.6 (see
-- Data.Nat.Properties.+-rightIdentity).
+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = succCong (+-rightIdentity n)

-- Adapted from the Agda standard library_0.6 (see
-- Data.Nat.Properties.+-assoc).
+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero     _ _ = refl
+-assoc (succ m) n o = succCong (+-assoc m n o)

-- Adapted from the Agda standard library 0.6 (see
-- Data.Nat.Properties.m+1+n≡1+m+n).
x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero     _ = refl
x+Sy≡S[x+y] (succ m) n = succCong (x+Sy≡S[x+y] m n)

-- Adapted from the Agda standard library 0.6 (see
-- Data.Nat.Properties.+-comm).
+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n = succ (m + n) ≡⟨ succCong (+-comm m n) ⟩
                    succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
                    n + succ m   ∎
