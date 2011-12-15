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
  begin
    b              ≡⟨ sym (leftIdentity b) ⟩
    ε · b          ≡⟨ subst (λ t → ε · b ≡ t · b )
                            (sym (leftInverse a))
                            refl
                   ⟩
    a ⁻¹ · a · b  ≡⟨ assoc (a ⁻¹) a b ⟩
    a ⁻¹ · (a · b)
  ∎

-- Adapted from the standard library.
x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
x≡[xy]y⁻¹ a b =
  begin
    a              ≡⟨ sym (rightIdentity a) ⟩
    a · ε          ≡⟨ subst (λ t → a · ε ≡ a · t )
                            (sym (rightInverse b))
                            refl
                   ⟩
    a · (b · b ⁻¹) ≡⟨ sym (assoc a b (b ⁻¹)) ⟩
    a · b · b ⁻¹
  ∎

rightIdentityUnique : ∃ λ u → (∀ x → x · u ≡ x) ∧
                              (∀ u' → (∀ x → x · u' ≡ x) → u ≡ u')
rightIdentityUnique =
-- Paper proof:
-- 1.  We know that ε is a right identity.
-- 2.  Let suppose there is other right identity u', i.e. ∀ x → xu' ≡ x, then
-- 2.1 ε   = εu'  (Hypothesis)
-- 2.2 εu' = u    (Left identity)
-- 2.3 ε   = u    (Transitivity)
  ε , rightIdentity , λ u' hyp → trans (sym (hyp ε)) (leftIdentity u')

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
rightIdentityUnique' : ∀ x u → x · u ≡ x → ε ≡ u
rightIdentityUnique' x u xu≡x =
  begin
    ε              ≡⟨ sym (leftInverse x) ⟩
    x ⁻¹ · x       ≡⟨ subst (λ t → x ⁻¹ · x ≡ x ⁻¹ · t )
                            (sym xu≡x)
                            refl
                   ⟩
    x ⁻¹ · (x · u) ≡⟨ sym (y≡x⁻¹[xy] x u) ⟩
    u
  ∎

leftIdentityUnique : ∃ λ u → (∀ x → u · x ≡ x) ∧
                             (∀ u' → (∀ x → u' · x ≡ x) → u ≡ u')
leftIdentityUnique =
-- Paper proof:
-- 1.  We know that ε is a left identity.
-- 2.  Let's suppose there is other left identity u', i.e. ∀ x → u'x ≡ x, then
-- 2.1 ε   = u'ε  (Hypothesis)
-- 2.2 u'ε = u    (Right identity)
-- 2.3 ε   = u    (Transitivity)
  ε , leftIdentity , λ u' hyp → trans (sym (hyp ε)) (rightIdentity u')

-- A more appropiate version to be used in the proofs.
-- Adapted from the standard library.
leftIdentityUnique' : ∀ x u → u · x ≡ x → ε ≡ u
leftIdentityUnique' x u ux≡x =
  begin
    ε              ≡⟨ sym (rightInverse x) ⟩
    x · x ⁻¹       ≡⟨ subst (λ t → x · x ⁻¹ ≡ t · x ⁻¹)
                            (sym ux≡x)
                            refl
                   ⟩
    u · x · x ⁻¹   ≡⟨ sym (x≡[xy]y⁻¹ u x) ⟩
    u
  ∎

rightCancellation : ∀ {x y z} → y · x ≡ z · x → y ≡ z
rightCancellation {x} {y} {z} yx≡zx =
-- Paper proof:
-- 1. (yx)x⁻¹  = (zx)x⁻¹  (Hypothesis xy = xz).
-- 2. (y)xx⁻¹  = (z)xx⁻¹  (Associative).
-- 3. yε       = zε       (Right inverse).
-- 4. y        = z        (Right identity).
  begin
    y              ≡⟨ sym (rightIdentity y) ⟩
    y · ε          ≡⟨ subst (λ t → y · ε ≡ y · t)
                            (sym (rightInverse x))
                            refl
                   ⟩
    y · (x · x ⁻¹) ≡⟨ sym (assoc y x (x ⁻¹)) ⟩
    y · x · x ⁻¹   ≡⟨ subst (λ t → y · x · x ⁻¹ ≡ t · x ⁻¹) yx≡zx refl ⟩
    z · x · x ⁻¹   ≡⟨ assoc z x (x ⁻¹) ⟩
    z · (x · x ⁻¹) ≡⟨ subst (λ t → z · (x · x ⁻¹) ≡ z · t)
                            (rightInverse x)
                            refl
                   ⟩
    z · ε          ≡⟨ rightIdentity z ⟩
    z
  ∎

leftCancellation : ∀ {x y z} → x · y ≡ x · z → y ≡ z
leftCancellation {x} {y} {z} xy≡xz =
-- Paper proof:
-- 1. x⁻¹(xy)  = x⁻¹(xz)  (Hypothesis xy = xz).
-- 2. x⁻¹x(y)  = x⁻¹x(z)  (Associative).
-- 3. εy       = εz       (Left inverse).
-- 4. y        = z        (Left identity).
  begin
    y              ≡⟨ sym (leftIdentity y) ⟩
    ε · y          ≡⟨ subst (λ t → ε · y ≡ t · y) (sym (leftInverse x)) refl ⟩
    x ⁻¹ · x · y   ≡⟨ assoc (x ⁻¹) x y ⟩
    x ⁻¹ · (x · y) ≡⟨ subst (λ t → x ⁻¹ · (x · y) ≡ x ⁻¹ · t) xy≡xz refl ⟩
    x ⁻¹ · (x · z) ≡⟨ sym (assoc (x ⁻¹) x z) ⟩
    x ⁻¹ · x · z   ≡⟨ subst (λ t → x ⁻¹ · x · z ≡ t · z) (leftInverse x) refl ⟩
    ε · z          ≡⟨ leftIdentity z ⟩
    z
  ∎

x≡y→xz≡yz : ∀ {a b c} → a ≡ b → a · c ≡ b · c
x≡y→xz≡yz refl = refl

x≡y→zx≡zy : ∀ {a b c} → a ≡ b → c · a ≡ c · b
x≡y→zx≡zy refl = refl

rightInverseUnique : ∀ {x} → ∃ λ r → (x · r ≡ ε) ∧
                                     (∀ r' → x · r' ≡ ε → r ≡ r')
rightInverseUnique {x} =
-- Paper proof:
-- 1.   We know that (x ⁻¹) is a right inverse for x.
-- 2.   Let's suppose there is other right inverse r for x, i.e. xr ≡ ε, then
-- 2.1. xx⁻¹ = ε  (Right inverse).
-- 2.2. xr   = ε  (Hypothesis).
-- 2.3. xx⁻¹ = xr (Transitivity).
-- 2.4  x⁻¹  = r  (Left cancellation).
  (x ⁻¹) , rightInverse x , prf
    where
    prf : ∀ r' → x · r' ≡ ε → x ⁻¹ ≡ r'
    prf r' xr'≡ε = leftCancellation xx⁻¹≡xr'
      where
      xx⁻¹≡xr' :  x · x ⁻¹ ≡ x · r'
      xx⁻¹≡xr' =
        begin
          x · x ⁻¹ ≡⟨ rightInverse x ⟩
          ε        ≡⟨ sym xr'≡ε ⟩
          x · r'
        ∎

-- A more appropiate version to be used in the proofs.
rightInverseUnique' : ∀ {x r} → x · r ≡ ε → x ⁻¹ ≡ r
rightInverseUnique' {x} {r} xr≡ε = leftCancellation xx⁻¹≡xr
  where
  xx⁻¹≡xr :  x · x ⁻¹ ≡ x · r
  xx⁻¹≡xr =
    begin
      x · x ⁻¹ ≡⟨ rightInverse x ⟩
      ε        ≡⟨ sym xr≡ε ⟩
      x · r
    ∎

leftInverseUnique : ∀ {x} → ∃ λ l → (l · x ≡ ε) ∧
                                    (∀ l' → l' · x ≡ ε → l ≡ l')
leftInverseUnique {x} =
-- Paper proof:
-- 1.   We know that (x ⁻¹) is a left inverse for x.
-- 2.   Let's suppose there is other right inverse l for x, i.e. lx ≡ ε, then
-- 2.1. x⁻¹x = ε  (Left inverse).
-- 2.2. lx   = ε  (Hypothesis).
-- 2.3. x⁻¹x = lx (Transitivity).
-- 2.4  x⁻¹  = l  (Right cancellation).
  (x ⁻¹) , leftInverse x , prf
    where
    prf : ∀ l' → l' · x ≡ ε → x ⁻¹ ≡ l'
    prf l' l'x≡ε = rightCancellation x⁻¹x≡l'x
      where
      x⁻¹x≡l'x : x ⁻¹ · x ≡ l' · x
      x⁻¹x≡l'x =
        begin
          x ⁻¹ · x ≡⟨ leftInverse x ⟩
          ε        ≡⟨ sym l'x≡ε ⟩
          l' · x
        ∎

-- A more appropiate version to be used in the proofs.
leftInverseUnique' : ∀ {x l} → l · x ≡ ε → x ⁻¹ ≡ l
leftInverseUnique' {x} {l} lx≡ε = rightCancellation x⁻¹x≡lx
  where
  x⁻¹x≡lx : x ⁻¹ · x ≡ l · x
  x⁻¹x≡lx =
    begin
      x ⁻¹ · x ≡⟨ leftInverse x ⟩
      ε        ≡⟨ sym lx≡ε ⟩
      l · x
    ∎

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≡ x
-- Paper proof:
-- 1. x⁻¹x = ε  (Left inverse).
-- 2. The previous equation states that x is the unique right
-- inverse (x⁻¹)⁻¹ of x⁻¹.
⁻¹-involutive x = rightInverseUnique' (leftInverse x)

identityInverse : ε ⁻¹ ≡ ε
-- Paper proof:
-- 1. εε = ε  (Left/Right identity).
-- 2. The previous equation states that ε is the unique left/right
-- inverse ε⁻¹ of ε.
identityInverse = rightInverseUnique' (leftIdentity ε)

inverseDistribution : ∀ x y → (x · y) ⁻¹ ≡ y ⁻¹ · x ⁻¹
-- Paper proof:
-- (y⁻¹x⁻¹)(xy) = y⁻¹(x ⁻¹(xy))  (Associative).
--              = y⁻¹(x ⁻¹x)y    (Associative).
--              = y⁻¹(εy)        (Left inverse).
--              = y⁻¹y           (Left identity).
--              = ε              (Left inverse)
-- Therefore, y⁻¹x⁻¹ is the unique left inverse of xy.
inverseDistribution x y = leftInverseUnique' y⁻¹x⁻¹[xy]≡ε
  where
  y⁻¹x⁻¹[xy]≡ε : y ⁻¹ · x ⁻¹ · (x · y) ≡ ε
  y⁻¹x⁻¹[xy]≡ε =
      begin
        y ⁻¹ · x ⁻¹ · (x · y)   ≡⟨ assoc (y ⁻¹) (x ⁻¹) (x · y) ⟩
        y ⁻¹ · (x ⁻¹ · (x · y)) ≡⟨ subst (λ t → y ⁻¹ · (x ⁻¹ · (x · y)) ≡
                                                y ⁻¹ · t)
                                         (sym (assoc (x ⁻¹) x y))
                                         refl
                                ⟩
        y ⁻¹ · (x ⁻¹ · x · y)   ≡⟨ subst (λ t → y ⁻¹ · (x ⁻¹ · x · y) ≡
                                                y ⁻¹ · (t · y))
                                         (leftInverse x)
                                         refl
                                ⟩
        y ⁻¹ · (ε · y)          ≡⟨ subst (λ t → y ⁻¹ · (ε · y) ≡ y ⁻¹ · t)
                                         (leftIdentity y)
                                         refl
                                ⟩
        y ⁻¹ · y                ≡⟨ leftInverse y ⟩
        ε
      ∎

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
x²≡ε→comm hyp {b} {c} {d} bc≡d = sym d≡cb
  where
  db≡c : d · b ≡ c
  db≡c =
    begin
      d · b            ≡⟨ sym (rightIdentity (d · b)) ⟩
      d · b · ε        ≡⟨ subst (λ t → d · b · ε ≡ d · b · t)
                                (sym (hyp c))
                                refl
                        ⟩
      d · b · (c · c)   ≡⟨ assoc d b (c · c) ⟩
      d · (b · (c · c)) ≡⟨ subst (λ t → d · (b · (c · c)) ≡ d · t)
                                 (sym (assoc b c c))
                                 refl
                        ⟩
      d · ((b · c) · c) ≡⟨ subst (λ t → d · ((b · c) · c) ≡ d · t)
                                 (subst (λ t → (b · c) · c ≡ t · c )
                                        bc≡d
                                        refl
                                 )
                                 refl
                        ⟩
      d · (d · c)       ≡⟨ sym (assoc d d c) ⟩
      d · d · c         ≡⟨ subst (λ t → d · d · c ≡ t · c )
                                 (hyp d)
                                 refl
                        ⟩
      ε · c             ≡⟨ leftIdentity c ⟩
      c
    ∎

  d≡cb : d ≡ c · b
  d≡cb =
    begin
      d           ≡⟨ sym (rightIdentity d) ⟩
      d · ε       ≡⟨ subst (λ t → d · ε ≡ d · t)
                           (sym (hyp b))
                           refl ⟩
      d · (b · b) ≡⟨ sym (assoc d b b) ⟩
      d · b · b   ≡⟨ x≡y→xz≡yz db≡c ⟩
      c · b
    ∎
