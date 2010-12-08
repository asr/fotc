------------------------------------------------------------------------------
-- Group theory properties (using equational reasoning)
------------------------------------------------------------------------------

module GroupTheory.PropertiesER where

open import GroupTheory.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

------------------------------------------------------------------------------

rightIdentityUnique : ∃D λ u → (∀ x → x ∙ u ≡ x) ∧
                               (∀ u' → (∀ x → x ∙ u' ≡ x) → u ≡ u')
rightIdentityUnique =
-- Paper proof:
-- 1.  We know that ε is a right identity.
-- 2.  Let suppose there is other right identity u', i.e. ∀ x → xu' ≡ x, then
-- 2.1 ε   = εu'  (Hypothesis)
-- 2.2 εu' = u    (Left identity)
-- 2.3 ε   = u    (Transitivity)
  ε , rightIdentity , λ u' hyp → trans (sym (hyp ε)) (leftIdentity u')

leftIdentityUnique : ∃D λ u → (∀ x → u ∙ x ≡ x) ∧
                              (∀ u' → (∀ x → u' ∙ x ≡ x) → u ≡ u')
leftIdentityUnique =
-- Paper proof:
-- 1.  We know that ε is a left identity.
-- 2.  Let's suppose there is other left identity u', i.e. ∀ x → u'x ≡ x, then
-- 2.1 ε   = u'ε  (Hypothesis)
-- 2.2 u'ε = u    (Right identity)
-- 2.3 ε   = u    (Transitivity)
  ε , leftIdentity , λ u' hyp → trans (sym (hyp ε)) (rightIdentity u')

rightCancellation : ∀ {x y z} → y ∙ x ≡ z ∙ x → y ≡ z
rightCancellation {x} {y} {z} yx≡zx =
-- Paper proof:
-- 1. (yx)x⁻¹  = (zx)x⁻¹  (Hypothesis xy = xz).
-- 2. (y)xx⁻¹  = (z)xx⁻¹  (Associative).
-- 3. yε       = zε       (Right inverse).
-- 4. y        = z        (Right identity).
  begin
    y              ≡⟨ sym (rightIdentity y) ⟩
    y ∙ ε          ≡⟨ subst (λ t → y ∙ ε ≡ y ∙ t)
                            (sym (rightInverse x))
                            refl
                   ⟩
    y ∙ (x ∙ x ⁻¹) ≡⟨ sym (assoc y x (x ⁻¹)) ⟩
    y ∙ x ∙ x ⁻¹   ≡⟨ subst (λ t → y ∙ x ∙ x ⁻¹ ≡ t ∙ x ⁻¹) yx≡zx refl ⟩
    z ∙ x ∙ x ⁻¹   ≡⟨ assoc z x (x ⁻¹) ⟩
    z ∙ (x ∙ x ⁻¹) ≡⟨ subst (λ t → z ∙ (x ∙ x ⁻¹) ≡ z ∙ t)
                            (rightInverse x)
                            refl
                   ⟩
    z ∙ ε          ≡⟨ rightIdentity z ⟩
    z
  ∎

leftCancellation : ∀ {x y z} → x ∙ y ≡ x ∙ z → y ≡ z
leftCancellation {x} {y} {z} xy≡xz =
-- Paper proof:
-- 1. x⁻¹ (xy) = x⁻¹(xz)  (Hypothesis xy = xz).
-- 2. x⁻¹x(y)  = x⁻¹x(z)  (Associative)-
-- 3. εy       = εz       (Left inverse).
-- 4. y        = z        (Left identity).
  begin
    y              ≡⟨ sym (leftIdentity y) ⟩
    ε ∙ y          ≡⟨ subst (λ t → ε ∙ y ≡ t ∙ y) (sym (leftInverse x)) refl ⟩
    x ⁻¹ ∙ x ∙ y   ≡⟨ assoc (x ⁻¹) x y ⟩
    x ⁻¹ ∙ (x ∙ y) ≡⟨ subst (λ t → x ⁻¹ ∙ (x ∙ y) ≡ x ⁻¹ ∙ t) xy≡xz refl ⟩
    x ⁻¹ ∙ (x ∙ z) ≡⟨ sym (assoc (x ⁻¹) x z) ⟩
    x ⁻¹ ∙ x ∙ z   ≡⟨ subst (λ t → x ⁻¹ ∙ x ∙ z ≡ t ∙ z) (leftInverse x) refl ⟩
    ε ∙ z          ≡⟨ leftIdentity z ⟩
    z
  ∎

rightInverseUnique : ∀ {x} → ∃D λ r → (x ∙ r ≡ ε) ∧
                                      (∀ r' → x ∙ r' ≡ ε → r ≡ r')
rightInverseUnique {x} =
-- Paper proof:
-- 1.   We know that (x ⁻¹) is a right inverse for x.
-- 2.   Let's suppose there is other right inverse r for x, i.e. xr ≡ ε, then
-- 2.1. xx⁻¹ = ε  (Right inverse).
-- 2.2. xr   = ε  (Hypothesis).
-- 2.3. xx⁻¹ = xr (Transitivity).
-- 2.4  x⁻¹  = r  (Left cancellation).
  (x ⁻¹) , rightInverse x , λ r' hyp → leftCancellation
    ( begin
        x ∙ x ⁻¹ ≡⟨ rightInverse x ⟩
        ε        ≡⟨ sym hyp ⟩
        x ∙ r'
      ∎
    )

-- A more appropiate version to be used in the proofs.
rightInverseUnique' : ∀ {x r} → x ∙ r ≡ ε → x ⁻¹ ≡ r
rightInverseUnique' {x} {r} = λ hyp → leftCancellation
  ( begin
      x ∙ x ⁻¹ ≡⟨ rightInverse x ⟩
      ε        ≡⟨ sym hyp ⟩
      x ∙ r
    ∎
  )

leftInverseUnique : ∀ {x} → ∃D λ l → (l ∙ x ≡ ε) ∧
                                     (∀ l' → l' ∙ x ≡ ε → l ≡ l')
leftInverseUnique {x} =
-- Paper proof:
-- 1.   We know that (x ⁻¹) is a left inverse for x.
-- 2.   Let's suppose there is other right inverse l for x, i.e. lx ≡ ε, then
-- 2.1. x⁻¹x = ε  (Left inverse).
-- 2.2. lx   = ε  (Hypothesis).
-- 2.3. x⁻¹x = lx (Transitivity).
-- 2.4  x⁻¹  = l  (Right cancellation).
  (x ⁻¹) , leftInverse x , λ l' hyp → rightCancellation
    ( begin
        x ⁻¹ ∙ x ≡⟨ leftInverse x ⟩
        ε ≡⟨ sym hyp ⟩
        l' ∙ x
      ∎
    )

-- A more appropiate version to be used in the proofs.
leftInverseUnique' : ∀ {x l} → l ∙ x ≡ ε → x ⁻¹ ≡ l
leftInverseUnique' {x} {l} = λ hyp → rightCancellation
  ( begin
      x ⁻¹ ∙ x ≡⟨ leftInverse x ⟩
      ε        ≡⟨ sym hyp ⟩
      l ∙ x
    ∎
  )

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

inverseDistribution : ∀ x y → (x ∙ y) ⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
-- Paper proof:
-- (y⁻¹x⁻¹)(xy) = y⁻¹(x ⁻¹(xy))  (Associative).
--              = y⁻¹(x ⁻¹x)y    (Associative).
--              = y⁻¹(εy)        (Left inverse).
--              = y⁻¹y           (Left identity).
--              = ε              (Left inverse)
-- Therefore, y⁻¹x⁻¹ is the unique left inverse of xy.
inverseDistribution x y = leftInverseUnique' y⁻¹x⁻¹[xy]≡ε
  where
    y⁻¹x⁻¹[xy]≡ε : y ⁻¹ ∙ x ⁻¹ ∙ (x ∙ y) ≡ ε
    y⁻¹x⁻¹[xy]≡ε =
        begin
          y ⁻¹ ∙ x ⁻¹ ∙ (x ∙ y)   ≡⟨ assoc (y ⁻¹) (x ⁻¹) (x ∙ y) ⟩
          y ⁻¹ ∙ (x ⁻¹ ∙ (x ∙ y)) ≡⟨ subst (λ t → y ⁻¹ ∙ (x ⁻¹ ∙ (x ∙ y)) ≡
                                                  y ⁻¹ ∙ t)
                                           (sym (assoc (x ⁻¹) x y))
                                           refl
                                  ⟩
          y ⁻¹ ∙ (x ⁻¹ ∙ x ∙ y)   ≡⟨ subst (λ t → y ⁻¹ ∙ (x ⁻¹ ∙ x ∙ y) ≡
                                                  y ⁻¹ ∙ (t ∙ y))
                                           (leftInverse x)
                                           refl
                                  ⟩
          y ⁻¹ ∙ (ε ∙ y)          ≡⟨ subst (λ t → y ⁻¹ ∙ (ε ∙ y) ≡ y ⁻¹ ∙ t)
                                           (leftIdentity y)
                                           refl
                                  ⟩
          y ⁻¹ ∙ y                ≡⟨ leftInverse y ⟩
          ε
        ∎
