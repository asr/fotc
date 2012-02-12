------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.PropertiesI where

open import GroupTheory.Base
open import GroupTheory.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- Adapted from the standard library.
y≡x⁻¹[xy] : ∀ a b → b ≡ a ⁻¹ · (a · b)
y≡x⁻¹[xy] a b =
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ ·-cong (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ∎

-- Adapted from the standard library.
x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
x≡[xy]y⁻¹ a b =
  a              ≡⟨ sym (rightIdentity a) ⟩
  a · ε          ≡⟨ ·-cong refl (sym (rightInverse b)) ⟩
  a · (b · b ⁻¹) ≡⟨ sym (assoc a b (b ⁻¹)) ⟩
  a · b · b ⁻¹ ∎

rightIdentityUnique : ∀ r → (∀ a → a · r ≡ a) → r ≡ ε
-- Paper proof (Saunders Mac Lane and Garret Birkhoff. Algebra. AMS
-- Chelsea Publishing, 3rd edition, 1999. p. 48):
--
-- 1. r  = εr (ε is an identity)
-- 2. εr = r  (hypothesis)
-- 3. r  = ε  (transitivity)
rightIdentityUnique r h = trans (sym (leftIdentity r)) (h ε)

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
rightIdentityUnique' : ∀ a r → a · r ≡ a → r ≡ ε
rightIdentityUnique' a r h =
  r              ≡⟨ y≡x⁻¹[xy] a r ⟩
  a ⁻¹ · (a · r) ≡⟨ ·-cong refl h ⟩
  a ⁻¹ · a       ≡⟨ leftInverse a ⟩
  ε ∎

leftIdentityUnique : ∀ l → (∀ a → l · a ≡ a) → l ≡ ε
-- Paper proof:
-- 1. l  = le (ε is an identity)
-- 2. le = e  (hypothesis)
-- 3. l  = e  (transitivity)
leftIdentityUnique l h = trans (sym (rightIdentity l)) (h ε)

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
leftIdentityUnique' : ∀ a l → l · a ≡ a → l ≡ ε
leftIdentityUnique' a l h =
  l            ≡⟨ x≡[xy]y⁻¹ l a ⟩
  l · a · a ⁻¹ ≡⟨ ·-cong h refl ⟩
  a · a ⁻¹     ≡⟨ rightInverse a ⟩
  ε ∎

rightCancellation : ∀ {a b c} → b · a ≡ c · a → b ≡ c
rightCancellation {a} {b} {c} h =
-- Paper proof:
-- 1. (ba)a⁻¹  = (ca)a⁻¹  (hypothesis ab = ac)
-- 2. (b)aa⁻¹  = (c)aa⁻¹  (associative axiom)
-- 3. bε       = cε       (right-inverse axiom for a⁻¹)
-- 4. b        = c        (right-identity axiom)
  b              ≡⟨ sym (rightIdentity b) ⟩
  b · ε          ≡⟨ ·-cong refl (sym (rightInverse a)) ⟩
  b · (a · a ⁻¹) ≡⟨ sym (assoc b a (a ⁻¹)) ⟩
  b · a · a ⁻¹   ≡⟨ ·-cong h refl ⟩
  c · a · a ⁻¹   ≡⟨ assoc c a (a ⁻¹) ⟩
  c · (a · a ⁻¹) ≡⟨ ·-cong refl (rightInverse a) ⟩
  c · ε          ≡⟨ rightIdentity c ⟩
  c ∎

leftCancellation : ∀ {a b c} → a · b ≡ a · c → b ≡ c
leftCancellation {a} {b} {c} h =
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ ·-cong (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ≡⟨ ·-cong refl h ⟩
  a ⁻¹ · (a · c) ≡⟨ sym (assoc (a ⁻¹) a c) ⟩
  a ⁻¹ · a · c   ≡⟨ ·-cong (leftInverse a) refl ⟩
  ε · c          ≡⟨ leftIdentity c ⟩
  c ∎

-- A different proof without using congruence.
leftCancellation₁ : ∀ {a b c} → a · b ≡ a · c → b ≡ c
leftCancellation₁ {a} {b} {c} h =
-- Paper proof:
-- 1. a⁻¹(ab)  = a⁻¹(ac)  (hypothesis ab = ac)
-- 2. a⁻¹a(b)  = a⁻¹a(c)  (associative axiom)
-- 3. εb       = εc       (left-inverse axiom for a⁻¹)
-- 4. b        = c        (left-identity axiom)
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ subst (λ t → ε · b ≡ t · b) (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ≡⟨ subst (λ t → a ⁻¹ · (a · b) ≡ a ⁻¹ · t) h refl ⟩
  a ⁻¹ · (a · c) ≡⟨ sym (assoc (a ⁻¹) a c) ⟩
  a ⁻¹ · a · c   ≡⟨ subst (λ t → a ⁻¹ · a · c ≡ t · c) (leftInverse a) refl ⟩
  ε · c          ≡⟨ leftIdentity c ⟩
  c ∎

rightInverseUnique : ∀ {a} → ∃[ r ] (a · r ≡ ε) ∧
                                    (∀ r' → a · r' ≡ ε → r ≡ r')
rightInverseUnique {a} =
-- Paper proof:
-- 1.   We know that (a⁻¹) is a right inverse for a.
-- 2.   Let's suppose there is other right inverse r for a, i.e. ar ≡ ε, then
-- 2.1. aa⁻¹ = ε  (right-inverse axiom)
-- 2.2. ar   = ε  (hypothesis)
-- 2.3. aa⁻¹ = ar (transitivity)
-- 2.4  a⁻¹  = a  (left-cancellation)
  (a ⁻¹) , rightInverse a , prf
    where
    prf : ∀ r' → a · r' ≡ ε → a ⁻¹ ≡ r'
    prf r' ar'≡ε = leftCancellation aa⁻¹≡ar'
      where
      aa⁻¹≡ar' : a · a ⁻¹ ≡ a · r'
      aa⁻¹≡ar' = a · a ⁻¹ ≡⟨ rightInverse a ⟩
                 ε        ≡⟨ sym ar'≡ε ⟩
                 a · r' ∎

-- A more appropiate version to be used in the proofs.
rightInverseUnique' : ∀ {a r} → a · r ≡ ε → a ⁻¹ ≡ r
rightInverseUnique' {a} {r} ar≡ε = leftCancellation aa⁻¹≡ar
  where
  aa⁻¹≡ar : a · a ⁻¹ ≡ a · r
  aa⁻¹≡ar = a · a ⁻¹ ≡⟨ rightInverse a ⟩
            ε        ≡⟨ sym ar≡ε ⟩
            a · r ∎

leftInverseUnique : ∀ {a} → ∃[ l ] (l · a ≡ ε) ∧
                                   (∀ l' → l' · a ≡ ε → l ≡ l')
leftInverseUnique {a} =
-- Paper proof:
-- 1.   We know that (a⁻¹) is a left inverse for a.
-- 2.   Let's suppose there is other right inverse l for a, i.e. la ≡ ε, then
-- 2.1. a⁻¹a = ε  (left-inverse axiom)
-- 2.2. la   = ε  (hypothesis)
-- 2.3. a⁻¹a = la (transitivity)
-- 2.4  a⁻¹  = l  (right-cancellation)
  (a ⁻¹) , leftInverse a , prf
    where
    prf : ∀ l' → l' · a ≡ ε → a ⁻¹ ≡ l'
    prf l' l'a≡ε = rightCancellation a⁻¹a≡l'a
      where
      a⁻¹a≡l'a : a ⁻¹ · a ≡ l' · a
      a⁻¹a≡l'a = a ⁻¹ · a ≡⟨ leftInverse a ⟩
                 ε        ≡⟨ sym l'a≡ε ⟩
                 l' · a ∎

-- A more appropiate version to be used in the proofs.
leftInverseUnique' : ∀ {a l} → l · a ≡ ε → a ⁻¹ ≡ l
leftInverseUnique' {a} {l} la≡ε = rightCancellation a⁻¹a≡la
  where
  a⁻¹a≡la : a ⁻¹ · a ≡ l · a
  a⁻¹a≡la = a ⁻¹ · a ≡⟨ leftInverse a ⟩
            ε        ≡⟨ sym la≡ε ⟩
            l · a ∎

⁻¹-involutive : ∀ a → a ⁻¹ ⁻¹ ≡ a
-- Paper proof:
-- 1. a⁻¹a = ε  (left-inverse axiom)
-- 2. The previous equation states that a is the unique right
-- inverse (a⁻¹)⁻¹ of a⁻¹.
⁻¹-involutive a = rightInverseUnique' (leftInverse a)

identityInverse : ε ⁻¹ ≡ ε
-- Paper proof:
-- 1. εε = ε  (left/right-identity axiom)
-- 2. The previous equation states that ε is the unique left/right
-- inverse ε⁻¹ of ε.
identityInverse = rightInverseUnique' (leftIdentity ε)

inverseDistribution : ∀ a b → (a · b) ⁻¹ ≡ b ⁻¹ · a ⁻¹
-- Paper proof:
-- (b⁻¹a⁻¹)(ab) = b⁻¹(a⁻¹(ab))  (associative axiom)
--              = b⁻¹(a⁻¹a)b    (associative axiom)
--              = b⁻¹(εb)       (left-inverse axiom)
--              = b⁻¹b          (left-identity axiom)
--              = ε             (left-inverse axiom)
-- Therefore, b⁻¹a⁻¹ is the unique left inverse of ab.
inverseDistribution a b = leftInverseUnique' b⁻¹a⁻¹[ab]≡ε
  where
  b⁻¹a⁻¹[ab]≡ε : b ⁻¹ · a ⁻¹ · (a · b) ≡ ε
  b⁻¹a⁻¹[ab]≡ε =
    b ⁻¹ · a ⁻¹ · (a · b)
      ≡⟨ assoc (b ⁻¹) (a ⁻¹) (a · b) ⟩
    b ⁻¹ · (a ⁻¹ · (a · b))
      ≡⟨ ·-cong refl (sym (assoc (a ⁻¹) a b)) ⟩
    b ⁻¹ · (a ⁻¹ · a · b)
      ≡⟨ ·-cong refl (·-cong  (leftInverse a) refl) ⟩
    b ⁻¹ · (ε · b)
      ≡⟨ ·-cong refl (leftIdentity b) ⟩
    b ⁻¹ · b
      ≡⟨ leftInverse b ⟩
    ε ∎

-- If the square of every element is the identity, the system is commutative.
-- From: TPTP v5.3.0 problem GRP/GRP001-2.p.
x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
-- Paper proof:
-- 1. d(bc)  = dd  (hypothesis bc = d)
-- 2. d(bc)  = ε   (hypothesis dd = ε)
-- 3. d(bc)c = c   (by 2)
-- 4. db(cc) = c   (associativity axiom)
-- 5. db     = c   (hypothesis cc = ε)
-- 6. (db)b  = cb  (by 5)
-- 7. d(bb)  = cb  (associativity axiom)
-- 6. d      = cb  (hypothesis bb = ε)
x²≡ε→comm h {b} {c} {d} bc≡d = sym d≡cb
  where
  db≡c : d · b ≡ c
  db≡c =
    d · b
      ≡⟨ sym (rightIdentity (d · b)) ⟩
    d · b · ε
      ≡⟨ ·-cong refl (sym (h c)) ⟩
    d · b · (c · c)
      ≡⟨ assoc d b (c · c) ⟩
    d · (b · (c · c))
      ≡⟨ ·-cong refl (sym (assoc b c c)) ⟩
    d · ((b · c) · c)
      ≡⟨ ·-cong refl (·-cong bc≡d refl) ⟩
    d · (d · c)
      ≡⟨ sym (assoc d d c) ⟩
    d · d · c
      ≡⟨ ·-cong (h d) refl ⟩
    ε · c
      ≡⟨ leftIdentity c ⟩
    c ∎

  d≡cb : d ≡ c · b
  d≡cb =
    d           ≡⟨ sym (rightIdentity d) ⟩
    d · ε       ≡⟨ ·-cong refl (sym (h b)) ⟩
    d · (b · b) ≡⟨ sym (assoc d b b) ⟩
    d · b · b   ≡⟨ ·-cong db≡c refl ⟩
    c · b ∎
