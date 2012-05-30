------------------------------------------------------------------------------
-- Testing an instance of the class DropVar: Lam term
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.DropVarLamTerm where

-- We add 3 to the fixities of the standard library.
infixr 8 _∷_
infixr 7 _,_
infix  7 _≡_ _≈_
infixr 5 _∧_

------------------------------------------------------------------------------

postulate
  D      : Set
  _∷_    : D → D → D
  Stream : D → Set
  _≈_    : D → D → Set

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

data ∃ (A : D → Set) : Set where
  _,_ : (t : D) → A t → ∃ A

syntax ∃ (λ x → e) = ∃[ x ] e

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
  Stream-gfp₂ : (P : D → Set) →
                -- P is post-fixed point of StreamF.
                (∀ {xs} → P xs → ∃[ x' ] ∃[ xs' ] P xs' ∧ xs ≡ x' ∷ xs') →
                -- Stream is greater than P.
                ∀ {xs} → P xs → Stream xs

postulate
  ≈-gfp₁ : ∀ {xs ys} → xs ≈ ys →
           ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
{-# ATP axiom ≈-gfp₁ #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P helper (ys , xs≈ys)
  where
  P : D → Set
  P ws = ∃[ zs ] ws ≈ zs
  {-# ATP definition P #-}

  postulate
    helper : ∀ {ws} → P ws → ∃[ w' ] ∃[ ws' ] P ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove helper #-}
