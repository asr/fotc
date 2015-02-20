------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GroupTheory.PropertiesI where

open import GroupTheory.Base

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Congruence properties

-- The propositional equality is compatible with the binary operation.

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong refl = refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong refl = refl

-- The propositional equality is compatible with the inverse function.
⁻¹-cong : ∀ {a b} → a ≡ b → a ⁻¹ ≡ b ⁻¹
⁻¹-cong refl = refl

------------------------------------------------------------------------------

leftCancellation : ∀ {a b c} → a · b ≡ a · c → b ≡ c
leftCancellation {a} {b} {c} h =
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ ·-leftCong (sym (leftInverse a)) ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ≡⟨ ·-rightCong h ⟩
  a ⁻¹ · (a · c) ≡⟨ sym (assoc (a ⁻¹) a c) ⟩
  a ⁻¹ · a · c   ≡⟨ ·-leftCong (leftInverse a) ⟩
  ε · c          ≡⟨ leftIdentity c ⟩
  c              ∎

-- A different proof without using congruence.
leftCancellation' : ∀ {a b c} → a · b ≡ a · c → b ≡ c
-- Paper proof (Mac Lane and Garret Birkhoff 1999. p. 48):
--
-- 1. a⁻¹(ab) = a⁻¹(ac)  (hypothesis ab = ac)
-- 2. a⁻¹a(b) = a⁻¹a(c)  (associative axiom)
-- 3. εb      = εc       (left-inverse axiom for a⁻¹)
-- 4. b       = c        (left-identity axiom)
leftCancellation' {a} {b} {c} h =
  b              ≡⟨ sym (leftIdentity b) ⟩
  ε · b          ≡⟨ subst (λ t → ε · b ≡ t · b) (sym (leftInverse a)) refl ⟩
  a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
  a ⁻¹ · (a · b) ≡⟨ subst (λ t → a ⁻¹ · (a · b) ≡ a ⁻¹ · t) h refl ⟩
  a ⁻¹ · (a · c) ≡⟨ sym (assoc (a ⁻¹) a c) ⟩
  a ⁻¹ · a · c   ≡⟨ subst (λ t → a ⁻¹ · a · c ≡ t · c) (leftInverse a) refl ⟩
  ε · c          ≡⟨ leftIdentity c ⟩
  c              ∎

-- Mac Lane and Garret Birkhoff (1999) p. 50, exercise 6.
rightIdentity : ∀ a → a · ε ≡ a
rightIdentity a = leftCancellation prf
  where
  prf : a ⁻¹ · (a · ε) ≡ a ⁻¹ · a
  prf = a ⁻¹ · (a · ε) ≡⟨ sym (assoc (a ⁻¹) a ε) ⟩
        a ⁻¹ · a · ε   ≡⟨ ·-leftCong (leftInverse a) ⟩
        ε · ε          ≡⟨ leftIdentity ε ⟩
        ε              ≡⟨ sym (leftInverse a) ⟩
        a ⁻¹ · a       ∎

-- Mac Lane and Garret Birkhoff (1999) p. 50, exercise 6.
rightInverse : ∀ a → a · a ⁻¹ ≡ ε
rightInverse a = leftCancellation prf
  where
  prf : a ⁻¹ · (a · a ⁻¹) ≡ a ⁻¹ · ε
  prf = a ⁻¹ · (a · a ⁻¹) ≡⟨ sym (assoc (a ⁻¹) a (a ⁻¹)) ⟩
        a ⁻¹ · a · a ⁻¹   ≡⟨ ·-leftCong (leftInverse a) ⟩
        ε · a ⁻¹          ≡⟨ leftIdentity (a ⁻¹)  ⟩
        a ⁻¹              ≡⟨ sym (rightIdentity (a ⁻¹)) ⟩
        a ⁻¹ · ε          ∎

rightCancellation : ∀ {a b c} → b · a ≡ c · a → b ≡ c
rightCancellation {a} {b} {c} h =
-- Paper proof:
--
-- 1. (ba)a⁻¹ = (ca)a⁻¹  (hypothesis ab = ac)
-- 2. (b)aa⁻¹ = (c)aa⁻¹  (associative axiom)
-- 3. bε      = cε       (right-inverse axiom for a⁻¹)
-- 4. b       = c        (right-identity axiom)
  b              ≡⟨ sym (rightIdentity b) ⟩
  b · ε          ≡⟨ ·-rightCong (sym (rightInverse a)) ⟩
  b · (a · a ⁻¹) ≡⟨ sym (assoc b a (a ⁻¹)) ⟩
  b · a · a ⁻¹   ≡⟨ ·-leftCong h ⟩
  c · a · a ⁻¹   ≡⟨ assoc c a (a ⁻¹) ⟩
  c · (a · a ⁻¹) ≡⟨ ·-rightCong (rightInverse a) ⟩
  c · ε          ≡⟨ rightIdentity c ⟩
  c              ∎

-- Adapted from the Agda standard library 0.8.1 (see
-- Algebra.Properties.Group.right-helper).
y≡x⁻¹[xy] : ∀ a b → b ≡ a ⁻¹ · (a · b)
y≡x⁻¹[xy] a b = b              ≡⟨ sym (leftIdentity b) ⟩
                ε · b          ≡⟨ ·-leftCong (sym (leftInverse a)) ⟩
                a ⁻¹ · a · b   ≡⟨ assoc (a ⁻¹) a b ⟩
                a ⁻¹ · (a · b) ∎

-- Adapted from the Agda standard library 0.8.1 (see
-- Algebra.Properties.Group.left-helper).
x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
x≡[xy]y⁻¹ a b = a              ≡⟨ sym (rightIdentity a) ⟩
                a · ε          ≡⟨ ·-rightCong (sym (rightInverse b)) ⟩
                a · (b · b ⁻¹) ≡⟨ sym (assoc a b (b ⁻¹)) ⟩
                a · b · b ⁻¹   ∎

rightIdentityUnique : ∀ r → (∀ a → a · r ≡ a) → r ≡ ε
-- Paper proof (Mac Lane and Garret 1999. p. 48):
--
-- 1. r  = εr (ε is an identity)
-- 2. εr = r  (hypothesis)
-- 3. r  = ε  (transitivity)
rightIdentityUnique r h = trans (sym (leftIdentity r)) (h ε)

-- A more appropiate version to be used in the proofs. Adapted from
-- the Agda standard library 0.8.1 (see
-- Algebra.Properties.Group.right-identity-unique).
rightIdentityUnique' : ∀ a r → a · r ≡ a → r ≡ ε
rightIdentityUnique' a r h = r              ≡⟨ y≡x⁻¹[xy] a r ⟩
                             a ⁻¹ · (a · r) ≡⟨ ·-rightCong h ⟩
                             a ⁻¹ · a       ≡⟨ leftInverse a ⟩
                             ε              ∎

leftIdentityUnique : ∀ l → (∀ a → l · a ≡ a) → l ≡ ε
-- Paper proof:
-- 1. l  = le (ε is an identity)
-- 2. le = e  (hypothesis)
-- 3. l  = e  (transitivity)
leftIdentityUnique l h = trans (sym (rightIdentity l)) (h ε)

-- A more appropiate version to be used in the proofs. Adapted from
-- the Agda standard library 0.8.1 (see
-- Algebra.Properties.Group.left-identity-unique).
leftIdentityUnique' : ∀ a l → l · a ≡ a → l ≡ ε
leftIdentityUnique' a l h = l            ≡⟨ x≡[xy]y⁻¹ l a ⟩
                            l · a · a ⁻¹ ≡⟨ ·-leftCong h ⟩
                            a · a ⁻¹     ≡⟨ rightInverse a ⟩
                            ε            ∎

rightInverseUnique : ∀ {a} → ∃[ r ] (a · r ≡ ε) ∧
                                    (∀ r' → a · r' ≡ ε → r ≡ r')
rightInverseUnique {a} =
-- Paper proof:
--
-- 1.   We know that (a⁻¹) is a right inverse for a.
-- 2.   Let's suppose there is other right inverse r for a, i.e. ar ≡ ε, then
-- 2.1. aa⁻¹ = ε  (right-inverse axiom)
-- 2.2. ar   = ε  (hypothesis)
-- 2.3. aa⁻¹ = ar (transitivity)
-- 2.4  a⁻¹  = a  (left-cancellation)
  _ , rightInverse a , prf
    where
    prf : ∀ r' → a · r' ≡ ε → a ⁻¹ ≡ r'
    prf r' ar'≡ε = leftCancellation aa⁻¹≡ar'
      where
      aa⁻¹≡ar' : a · a ⁻¹ ≡ a · r'
      aa⁻¹≡ar' = a · a ⁻¹ ≡⟨ rightInverse a ⟩
                 ε        ≡⟨ sym ar'≡ε ⟩
                 a · r'   ∎

-- A more appropiate version to be used in the proofs.
rightInverseUnique' : ∀ {a r} → a · r ≡ ε → a ⁻¹ ≡ r
rightInverseUnique' {a} {r} ar≡ε = leftCancellation aa⁻¹≡ar
  where
  aa⁻¹≡ar : a · a ⁻¹ ≡ a · r
  aa⁻¹≡ar = a · a ⁻¹ ≡⟨ rightInverse a ⟩
            ε        ≡⟨ sym ar≡ε ⟩
            a · r    ∎

leftInverseUnique : ∀ {a} → ∃[ l ] (l · a ≡ ε) ∧
                                   (∀ l' → l' · a ≡ ε → l ≡ l')
leftInverseUnique {a} =
-- Paper proof:
--
-- 1.   We know that (a⁻¹) is a left inverse for a.
-- 2.   Let's suppose there is other right inverse l for a, i.e. la ≡ ε, then
-- 2.1. a⁻¹a = ε  (left-inverse axiom)
-- 2.2. la   = ε  (hypothesis)
-- 2.3. a⁻¹a = la (transitivity)
-- 2.4  a⁻¹  = l  (right-cancellation)
  _ , leftInverse a , prf
    where
    prf : ∀ l' → l' · a ≡ ε → a ⁻¹ ≡ l'
    prf l' l'a≡ε = rightCancellation a⁻¹a≡l'a
      where
      a⁻¹a≡l'a : a ⁻¹ · a ≡ l' · a
      a⁻¹a≡l'a = a ⁻¹ · a ≡⟨ leftInverse a ⟩
                 ε        ≡⟨ sym l'a≡ε ⟩
                 l' · a   ∎

-- A more appropiate version to be used in the proofs.
leftInverseUnique' : ∀ {a l} → l · a ≡ ε → a ⁻¹ ≡ l
leftInverseUnique' {a} {l} la≡ε = rightCancellation a⁻¹a≡la
  where
  a⁻¹a≡la : a ⁻¹ · a ≡ l · a
  a⁻¹a≡la = a ⁻¹ · a ≡⟨ leftInverse a ⟩
            ε        ≡⟨ sym la≡ε ⟩
            l · a    ∎

⁻¹-involutive : ∀ a → a ⁻¹ ⁻¹ ≡ a
-- Paper proof:
--
-- 1. a⁻¹a = ε  (left-inverse axiom)
-- 2. The previous equation states that a is the unique right
-- inverse (a⁻¹)⁻¹ of a⁻¹.
⁻¹-involutive a = rightInverseUnique' (leftInverse a)

identityInverse : ε ⁻¹ ≡ ε
-- Paper proof:
--
-- 1. εε = ε  (left/right-identity axiom)
-- 2. The previous equation states that ε is the unique left/right
-- inverse ε⁻¹ of ε.
identityInverse = rightInverseUnique' (leftIdentity ε)

inverseDistribution : ∀ a b → (a · b) ⁻¹ ≡ b ⁻¹ · a ⁻¹
-- Paper proof:
--
-- (b⁻¹a⁻¹)(ab) = b⁻¹(a⁻¹(ab)) (associative axiom)
--              = b⁻¹(a⁻¹a)b   (associative axiom)
--              = b⁻¹(εb)      (left-inverse axiom)
--              = b⁻¹b         (left-identity axiom)
--              = ε            (left-inverse axiom)
-- Therefore, b⁻¹a⁻¹ is the unique left inverse of ab.
inverseDistribution a b = leftInverseUnique' b⁻¹a⁻¹[ab]≡ε
  where
  b⁻¹a⁻¹[ab]≡ε : b ⁻¹ · a ⁻¹ · (a · b) ≡ ε
  b⁻¹a⁻¹[ab]≡ε =
    b ⁻¹ · a ⁻¹ · (a · b)
      ≡⟨ assoc (b ⁻¹) (a ⁻¹) (a · b) ⟩
    b ⁻¹ · (a ⁻¹ · (a · b))
      ≡⟨ ·-rightCong (sym (assoc (a ⁻¹) a b)) ⟩
    b ⁻¹ · (a ⁻¹ · a · b)
      ≡⟨ ·-rightCong (·-leftCong (leftInverse a)) ⟩
    b ⁻¹ · (ε · b)
      ≡⟨ ·-rightCong (leftIdentity b) ⟩
    b ⁻¹ · b
      ≡⟨ leftInverse b ⟩
    ε ∎

-- If the square of every element is the identity, the system is
-- commutative. From: TPTP 6.1.0 problem GRP/GRP001-2.p.
x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
-- Paper proof:
--
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
      ≡⟨ ·-rightCong (sym (h c)) ⟩
    d · b · (c · c)
      ≡⟨ assoc d b (c · c) ⟩
    d · (b · (c · c))
      ≡⟨ ·-rightCong (sym (assoc b c c)) ⟩
    d · ((b · c) · c)
      ≡⟨ ·-rightCong (·-leftCong bc≡d) ⟩
    d · (d · c)
      ≡⟨ sym (assoc d d c) ⟩
    d · d · c
      ≡⟨ ·-leftCong (h d) ⟩
    ε · c
      ≡⟨ leftIdentity c ⟩
    c ∎

  d≡cb : d ≡ c · b
  d≡cb = d           ≡⟨ sym (rightIdentity d) ⟩
         d · ε       ≡⟨ ·-rightCong (sym (h b)) ⟩
         d · (b · b) ≡⟨ sym (assoc d b b) ⟩
         d · b · b   ≡⟨ ·-leftCong db≡c ⟩
         c · b       ∎

------------------------------------------------------------------------------
-- References
--
-- Mac Lane, S. and Birkhof, G. (1999). Algebra. 3rd ed. AMS Chelsea
-- Publishing.
