module BisimilarityPostFixedPoint where

-- open import LTC.Minimal
-- open import LTC.MinimalER

infixr 5 _∷_
infix 4 _≈_
infixr 4 _,_
infix  3 _≡_
infixr 2 _∧_

------------------------------------------------------------------------------
-- LTC stuff

-- The universal domain.
postulate D : Set

  -- LTC lists.
postulate
  _∷_  : D → D → D

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P

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

------------------------------------------------------------------------------
BISI : (D → D → Set) → D → D → Set
BISI R xs ys =
  ∃D (λ x' →
  ∃D (λ y' →
  ∃D (λ xs' →
  ∃D (λ ys' →
     x' ≡ y' ∧ R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ y' ∷ ys'))))

-- From Peter email:

-- For the case of bisimilarity ≈ we have

-- (i) a post-fixed point of BISI, is the following first order axiom

-- forall xs,ys,x,y. x = y & xs ≈ ys -> x :: xs ≈ y :: ys

postulate
  -- The bisimilarity relation.
  _≈_ : D → D → Set

  -- The bisimilarity relation is a post-fixed point of BISI.
  -≈-gfp₁ : {x y xs ys : D} → x ≡ y ∧ xs ≈ ys → x ∷ xs ≈ y ∷ ys

foo : (xs ys : D) → xs ≈ ys → BISI _≈_ xs ys
foo xs ys xs≈ys = {!!}

bar : (xs ys : D) → BISI _≈_ xs ys → xs ≈ ys
bar xs ys (x' , y' , xs' , ys' , x'≡y' , xs'≈ys' , xs≡x'∷xs' , ys≡y'∷ys)
  = subst (λ t₁ → t₁ ≈ ys)
          (sym xs≡x'∷xs')
          (subst (λ t₂ → x' ∷ xs' ≈ t₂)
                 (sym ys≡y'∷ys)
                 (-≈-gfp₁ (x'≡y' , xs'≈ys')))
