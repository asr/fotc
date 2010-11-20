module BisimilarityPostulates where

-- open import LTC.Base
-- open import LTC.BaseER

infixr 8 _∷_
infix  7 _≈_
infixr 7 _,_
infix  6 _≡_
infixr 5 _∧_

------------------------------------------------------------------------------
-- LTC stuff

-- The universal domain.
postulate D : Set

  -- LTC lists.
postulate
  _∷_  : D → D → D

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _) = x

∃D-proj₂ : {P : D → Set}(∃p : ∃D P) → P (∃D-proj₁ ∃p)
∃D-proj₂ (_ , px) = px

-- The identity type on D.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Identity properties

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px

-- The conjunction data type.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y

------------------------------------------------------------------------------

BISI : (D → D → Set) → D → D → Set
BISI _R_ xs ys =
  ∃D (λ x' →
  ∃D (λ xs' →
  ∃D (λ ys' →
     xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))

postulate
  -- The bisimilarity relation.
  _≈_ : D → D → Set

  -- The bisimilarity relation is a post-fixed point of BISI
  -- (first-order version).
  -≈-gfp₁ : {xs ys : D} → xs ≈ ys →
            ∃D (λ x' →
            ∃D (λ xs' →
            ∃D (λ ys' → xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))

  -- The bisimilarity relation is the greatest post-fixed point of
  -- BISI (first-order version).
  -≈-gfp₂ : {_R_ : D → D → Set} →
            -- R is a post-fixed point of BISI.
            ({xs ys : D} → xs R ys →
              ∃D (λ x' →
              ∃D (λ xs' →
              ∃D (λ ys' → xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))) →
            -- ≈ is the greatest post-fixed point.
            {xs ys : D} → xs R ys → xs ≈ ys

-≈→BISI≈ : {xs ys : D} → xs ≈ ys → BISI _≈_ xs ys
-≈→BISI≈ xs≈ys = -≈-gfp₁ xs≈ys

R→BISI-R→R→≈ : {_R_ : D → D → Set} →
               ({xs ys : D} → xs R ys → BISI _R_ xs ys) →
               {xs ys : D} → xs R ys → xs ≈ ys
R→BISI-R→R→≈ pfp xsRys = -≈-gfp₂ pfp xsRys
