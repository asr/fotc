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
  ε · b          ≡⟨ subst (λ t → ε · b ≡ t · b ) (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ∎

-- Adapted from the standard library.
x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
x≡[xy]y⁻¹ a b =
  a              ≡⟨ sym (rightIdentity a) ⟩
  a · ε          ≡⟨ subst (λ t → a · ε ≡ a · t ) (sym (rightInverse b)) refl ⟩
  a · (b · b ⁻¹) ≡⟨ sym (assoc a b (b ⁻¹)) ⟩
  a · b · b ⁻¹ ∎

rightIdentityUnique : ∀ r → (∀ a → a · r ≡ a) → ε ≡ r
-- Paper proof:
-- 1.  We know that ε is a right identity.
-- 2.  Let suppose there is other right identity r, i.e. ∀ a → ar ≡ a, then
-- 2.1 ε  = εr  (Hypothesis)
-- 2.2 εr = r   (Left identity)
-- 2.3 ε  = r   (Transitivity)
rightIdentityUnique r h = trans (sym (h ε)) (leftIdentity r)

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
rightIdentityUnique' : ∀ a r → a · r ≡ a → ε ≡ r
rightIdentityUnique' a r h =
  ε              ≡⟨ sym (leftInverse a) ⟩
  a ⁻¹ · a       ≡⟨ subst (λ t → a ⁻¹ · a ≡ a ⁻¹ · t ) (sym h) refl ⟩
  a ⁻¹ · (a · r) ≡⟨ sym (y≡x⁻¹[xy] a r) ⟩
  r ∎

leftIdentityUnique : ∀ l → (∀ a → l · a ≡ a) → ε ≡ l
-- Paper proof:
-- 1.  We know that ε is a left identity.
-- 2.  Let's suppose there is other left identity l, i.e. ∀ a → la ≡ a, then
-- 2.1 ε  = lε  (Hypothesis)
-- 2.2 lε = l   (Right identity)
-- 2.3 ε  = l   (Transitivity)
leftIdentityUnique l h = trans (sym (h ε)) (rightIdentity l)

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
leftIdentityUnique' : ∀ a l → l · a ≡ a → ε ≡ l
leftIdentityUnique' a l h =
  ε              ≡⟨ sym (rightInverse a) ⟩
  a · a ⁻¹       ≡⟨ subst (λ t → a · a ⁻¹ ≡ t · a ⁻¹) (sym h) refl ⟩
  l · a · a ⁻¹   ≡⟨ sym (x≡[xy]y⁻¹ l a) ⟩
  l ∎

rightCancellation : ∀ {a b c} → b · a ≡ c · a → b ≡ c
rightCancellation {a} {b} {c} h =
-- Paper proof:
-- 1. (ba)a⁻¹  = (ca)a⁻¹  (Hypothesis ab = ac).
-- 2. (b)aa⁻¹  = (c)aa⁻¹  (Associative).
-- 3. bε       = cε       (Right inverse).
-- 4. b        = c        (Right identity).
  b              ≡⟨ sym (rightIdentity b) ⟩
  b · ε          ≡⟨ subst (λ t → b · ε ≡ b · t) (sym (rightInverse a)) refl ⟩
  b · (a · a ⁻¹) ≡⟨ sym (assoc b a (a ⁻¹)) ⟩
  b · a · a ⁻¹   ≡⟨ subst (λ t → b · a · a ⁻¹ ≡ t · a ⁻¹) h refl ⟩
  c · a · a ⁻¹   ≡⟨ assoc c a (a ⁻¹) ⟩
  c · (a · a ⁻¹) ≡⟨ subst (λ t → c · (a · a ⁻¹) ≡ c · t) (rightInverse a) refl ⟩
  c · ε          ≡⟨ rightIdentity c ⟩
  c ∎

leftCancellation : ∀ {a b c} → a · b ≡ a · c → b ≡ c
leftCancellation {a} {b} {c} h =
-- Paper proof:
-- 1. a⁻¹(ab)  = a⁻¹(ac)  (Hypothesis ab = ac).
-- 2. a⁻¹a(b)  = a⁻¹a(c)  (Associative).
-- 3. εb       = εc       (Left inverse).
-- 4. b        = c        (Left identity).
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ subst (λ t → ε · b ≡ t · b) (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ≡⟨ subst (λ t → a ⁻¹ · (a · b) ≡ a ⁻¹ · t) h refl ⟩
  a ⁻¹ · (a · c) ≡⟨ sym (assoc (a ⁻¹) a c) ⟩
  a ⁻¹ · a · c   ≡⟨ subst (λ t → a ⁻¹ · a · c ≡ t · c) (leftInverse a) refl ⟩
  ε · c          ≡⟨ leftIdentity c ⟩
  c ∎

x≡y→xz≡yz : ∀ {a b c} → a ≡ b → a · c ≡ b · c
x≡y→xz≡yz refl = refl

x≡y→zx≡zy : ∀ {a b c} → a ≡ b → c · a ≡ c · b
x≡y→zx≡zy refl = refl

rightInverseUnique : ∀ {a} → ∃[ r ] (a · r ≡ ε) ∧
                                    (∀ r' → a · r' ≡ ε → r ≡ r')
rightInverseUnique {a} =
-- Paper proof:
-- 1.   We know that (a⁻¹) is a right inverse for a.
-- 2.   Let's suppose there is other right inverse r for a, i.e. ar ≡ ε, then
-- 2.1. aa⁻¹ = ε  (Right inverse).
-- 2.2. ar   = ε  (Hypothesis).
-- 2.3. aa⁻¹ = ar (Transitivity).
-- 2.4  a⁻¹  = a  (Left cancellation).
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
-- 2.1. a⁻¹a = ε  (Left inverse).
-- 2.2. la   = ε  (Hypothesis).
-- 2.3. a⁻¹a = la (Transitivity).
-- 2.4  a⁻¹  = l  (Right cancellation).
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
-- 1. a⁻¹a = ε  (Left inverse).
-- 2. The previous equation states that a is the unique right
-- inverse (a⁻¹)⁻¹ of a⁻¹.
⁻¹-involutive a = rightInverseUnique' (leftInverse a)

identityInverse : ε ⁻¹ ≡ ε
-- Paper proof:
-- 1. εε = ε  (Left/Right identity).
-- 2. The previous equation states that ε is the unique left/right
-- inverse ε⁻¹ of ε.
identityInverse = rightInverseUnique' (leftIdentity ε)

inverseDistribution : ∀ a b → (a · b) ⁻¹ ≡ b ⁻¹ · a ⁻¹
-- Paper proof:
-- (b⁻¹a⁻¹)(ab) = b⁻¹(a⁻¹(ab))  (Associative).
--              = b⁻¹(a⁻¹a)b    (Associative).
--              = b⁻¹(εb)       (Left inverse).
--              = b⁻¹b          (Left identity).
--              = ε             (Left inverse)
-- Therefore, b⁻¹a⁻¹ is the unique left inverse of ab.
inverseDistribution a b = leftInverseUnique' b⁻¹a⁻¹[ab]≡ε
  where
  b⁻¹a⁻¹[ab]≡ε : b ⁻¹ · a ⁻¹ · (a · b) ≡ ε
  b⁻¹a⁻¹[ab]≡ε =
    b ⁻¹ · a ⁻¹ · (a · b)
      ≡⟨ assoc (b ⁻¹) (a ⁻¹) (a · b) ⟩
    b ⁻¹ · (a ⁻¹ · (a · b))
      ≡⟨ subst (λ t → b ⁻¹ · (a ⁻¹ · (a · b)) ≡ b ⁻¹ · t)
               (sym (assoc (a ⁻¹) a b))
               refl
      ⟩
    b ⁻¹ · (a ⁻¹ · a · b)
      ≡⟨ subst (λ t → b ⁻¹ · (a ⁻¹ · a · b) ≡ b ⁻¹ · (t · b))
               (leftInverse a)
               refl
      ⟩
    b ⁻¹ · (ε · b)
      ≡⟨ subst (λ t → b ⁻¹ · (ε · b) ≡ b ⁻¹ · t)
               (leftIdentity b)
               refl
      ⟩
    b ⁻¹ · b
      ≡⟨ leftInverse b ⟩
    ε ∎

-- If the square of every element is the identity, the system is commutative.
-- From: TPTP v5.3.0. File: Problems/GRP/GRP001-2.p
x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
-- Paper proof:
-- 1. d(bc)  = dd  (Hypothesis bc = d).
-- 2. d(bc)  = ε   (Hypothesis dd = ε).
-- 3. d(bc)c = c   (By 2).
-- 4. db(cc) = c   (Associativity).
-- 5. db     = c   (Hypothesis cc = ε).
-- 6. (db)b  = cb  (By 5).
-- 7. d(bb)  = cb  (Associativity).
-- 6. d      = cb  (Hypothesis bb = ε).
x²≡ε→comm h {b} {c} {d} bc≡d = sym d≡cb
  where
  db≡c : d · b ≡ c
  db≡c =
    d · b
      ≡⟨ sym (rightIdentity (d · b)) ⟩
    d · b · ε
      ≡⟨ subst (λ t → d · b · ε ≡ d · b · t) (sym (h c)) refl ⟩
    d · b · (c · c)
      ≡⟨ assoc d b (c · c) ⟩
    d · (b · (c · c))
      ≡⟨ subst (λ t → d · (b · (c · c)) ≡ d · t) (sym (assoc b c c)) refl ⟩
    d · ((b · c) · c)
      ≡⟨ subst (λ t → d · ((b · c) · c) ≡ d · t)
               (subst (λ t → (b · c) · c ≡ t · c )
                      bc≡d
                      refl
               )
               refl
      ⟩
    d · (d · c)
      ≡⟨ sym (assoc d d c) ⟩
    d · d · c
      ≡⟨ subst (λ t → d · d · c ≡ t · c ) (h d) refl ⟩
    ε · c
      ≡⟨ leftIdentity c ⟩
    c ∎

  d≡cb : d ≡ c · b
  d≡cb =
    d           ≡⟨ sym (rightIdentity d) ⟩
    d · ε       ≡⟨ subst (λ t → d · ε ≡ d · t) (sym (h b)) refl ⟩
    d · (b · b) ≡⟨ sym (assoc d b b) ⟩
    d · b · b   ≡⟨ x≡y→xz≡yz db≡c ⟩
    c · b ∎
