------------------------------------------------------------------------------
-- Bisimilarity properties
------------------------------------------------------------------------------

module BisimilarityProperties where

-- open import LTC.Minimal

-- open import LTC.Data.Stream.Bisimilarity

infixr 5 _∷_
infix  4 _≡_ _,_ _≈_
infixr 2 _∧_

------------------------------------------------------------------------------
-- LTC stuff

-- The universal domain.
postulate D : Set

-- The identity type on D.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Identity properties
sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _ ) = x

∃D-proj₂ : {P : D → Set} → (x-px : ∃D P) → P (∃D-proj₁ x-px)
∃D-proj₂ (_ , px) = px

-- The conjunction data type.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y

postulate
  -- LTC lists.
  []   : D
  _∷_  : D → D → D

postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys

------------------------------------------------------------------------------
-- Bisimilarity relation

-- Because the LTC is a first-order theory, we define a first-order
-- version of the bisimilarity relation.

-- The bisimilarity relation.
postulate
  _≈_ : D → D → Set

-- The bisimilarity relation is a post-fixed point of a bisimilar
-- relation.
postulate
  -≈-gfp₁ : {xs ys : D} → xs ≈ ys →
            ∃D (λ x' →
            ∃D (λ xs' →
            ∃D (λ ys' → xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))
-- {-# ATP axiom -≈-gfp₁ #-}

-- The bisimilarity relation is the greatest post-fixed point of a
-- bisimilar.

-- N.B. This is a second-order axiom. In the proofs, we *must* use an
-- axiom scheme instead. Therefore, we do not add this postulate as an
-- ATP axiom.
postulate
  -≈-gfp₂ : {_R_ : D → D → Set} →
            -- R is a post-fixed point of the bisimilar relation.
            ({xs ys : D} → xs R ys →
              ∃D (λ x' →
              ∃D (λ xs' →
              ∃D (λ ys' → xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))) →
            -- ≈ is greater than R.
           {xs ys : D} → xs R ys → xs ≈ ys

------------------------------------------------------------------------------
-- Properties

x∷xs≈x∷ys→xs≈ys : {x xs ys : D} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} x∷xs≈x∷ys = xs≈ys
  where
    x' : D
    x' = ∃D-proj₁ (-≈-gfp₁ x∷xs≈x∷ys)

    xs' : D
    xs' = ∃D-proj₁ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys))

    ys' : D
    ys' = ∃D-proj₁ (∃D-proj₂ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys)))

    aux : xs' ≈ ys' ∧ x ∷ xs ≡ x' ∷ xs' ∧ x ∷ ys ≡ x' ∷ ys'
    aux = ∃D-proj₂ (∃D-proj₂ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys)))

    xs'≈ys' : xs' ≈ ys'
    xs'≈ys' = ∧-proj₁ aux

    x∷xs≡x'∷xs' : x ∷ xs ≡ x' ∷ xs'
    x∷xs≡x'∷xs' = ∧-proj₁ (∧-proj₂ aux)

    x∷ys≡x'∷ys' : x ∷ ys ≡ x' ∷ ys'
    x∷ys≡x'∷ys' = ∧-proj₂ (∧-proj₂ aux)

    xs≡xs' : xs ≡ xs'
    xs≡xs' = ∧-proj₂ (∷-injective x∷xs≡x'∷xs')

    ys≡ys' : ys ≡ ys'
    ys≡ys' = ∧-proj₂ (∷-injective x∷ys≡x'∷ys')

    xs≈ys : xs ≈ ys
    xs≈ys = subst (λ t → t ≈ ys)
                  (sym xs≡xs')
                  (subst (λ t → xs' ≈ t) (sym ys≡ys') xs'≈ys')

xs≈ys→x∷xs≈x∷ys : {x xs ys : D} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
xs≈ys→x∷xs≈x∷ys {x} {xs} {ys} xs≈ys = {!!}
