-----------------------------------------------------------------------------
-- Existential elimination
-----------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.Common.FOL.Existential.Elimination where

-----------------------------------------------------------------------------

postulate D : Set

module ∃₁ where
  -- Type theoretical version

  -- We add 3 to the fixities of the Agda standard library 0.8.1 (see
  -- Data/Product.agda).
  infixr 7 _,_

  -- The existential quantifier type on D.
  data ∃ (A : D → Set) : Set where
    _,_ : (x : D) → A x → ∃ A

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  -- The existential proyections.
  ∃-proj₁ : ∀ {A} → ∃ A → D
  ∃-proj₁ (x , _) = x

  ∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
  ∃-proj₂ (_ , Ax) = Ax

  -- Some examples

  -- The order of quantifiers of the same sort is irrelevant.
  ∃-ord : {A² : D → D → Set} → (∃[ x ] ∃[ y ] A² x y) → (∃[ y ] ∃[ x ] A² x y)
  ∃-ord (x , y , h) = y , x , h

-----------------------------------------------------------------------------

module ∃₂ where
  -- First-order logic version

  -- We add 3 to the fixities of the Agda standard library 0.8.1 (see
  -- Data/Product.agda).
  infixr 7 _,_

  -- The existential quantifier type on D.
  data ∃ (A : D → Set) : Set where
    _,_ : (x : D) → A x → ∃ A

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  -- Existential elimination
  --     ∃x.A(x)   A(x) → B
  --  ------------------------
  --             B

  -- NB. We do not use the usual type theory elimination with two
  -- projections because we are working in first-order logic where we
  -- do need extract a witness from an existence proof.
  ∃-elim : {A : D → Set}{B : Set} → ∃ A → ((x : D) → A x → B) → B
  ∃-elim (x , Ax) h = h x Ax

  -- Some examples

  -- The order of quantifiers of the same sort is irrelevant.
  ∃-ord : {A² : D → D → Set} → (∃[ x ] ∃[ y ] A² x y) → (∃[ y ] ∃[ x ] A² x y)
  ∃-ord h = ∃-elim h (λ x h₁ → ∃-elim h₁ (λ y prf → y , x , prf))

  -- A proof non-FOL valid
  non-FOL : {A : D → Set} → ∃ A → D
  non-FOL h = ∃-elim h (λ x _ → x)

-----------------------------------------------------------------------------

module ∃₃ where
  -- First-order logic version

  -- A different version from the existential introduction
  --      A(x)
  --  ------------
  --     ∃x.A(x)

  -- The existential quantifier type on D.
  data ∃ (A : D → Set) : Set where
    ∃-intro : ((x : D) → A x) → ∃ A

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  postulate d : D

  -- Existential elimination.
  -- NB. It is neccesary that D ≢ ∅.
  ∃-elim : {A : D → Set}{B : Set} → ∃ A → ((x : D) → A x → B) → B
  ∃-elim (∃-intro h₁) h₂ = h₂ d (h₁ d)

  -- Some examples

  -- Impossible
  -- thm : {A : D → Set} → ∃[ x ] A x → ∃[ y ] A y
  -- thm h = ∃-elim h (λ x prf → {!!})
