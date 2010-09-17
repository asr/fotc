------------------------------------------------------------------------------
-- Bisimulation on LTC list
------------------------------------------------------------------------------

module LTC.Data.List.Bisimulation where

open import LTC.Minimal

open import LTC.Data.List using
  ( List ; consL ; nilL -- The LTC list type
  )
open import LTC.Minimal.Properties using ( ≡-list )

infix 4 _∼_ _≈_

------------------------------------------------------------------------------

-- The bisimulation on LTC list terms
postulate
  _∼_     : D → D → D
  ∼-[]-[] : [] ∼ []                           ≡ true
  ∼-[]-∷  : (x xs : D) → [] ∼ x ∷ xs          ≡ false
  ∼-∷-[]  : (x xs : D) → x ∷ xs ∼ []          ≡ false
  ∼-∷-∷   : (x xs ys : D) → x ∷ xs ∼ x ∷ ys   ≡ xs ∼ ys
{-# ATP axiom ∼-[]-[] #-}
{-# ATP axiom ∼-[]-∷ #-}
{-# ATP axiom ∼-∷-[] #-}
{-# ATP axiom ∼-∷-∷ #-}

-- The bisimulation relation
_≈_ : D → D → Set
xs ≈ ys = xs ∼ ys ≡ true
{-# ATP definition _≈_ #-}

-- It seems we cannot prove this theorem from the bisimulation axioms.
postulate
   ¬-≈ : (x y xs ys : D) → ¬ (x ≡ y) → ¬ ( x ∷ xs ≈ y ∷ ys)
{-# ATP axiom ¬-≈ #-}

-- Properties

≈-refl : {xs : D} → List xs → xs ≈ xs
≈-refl nilL               = ∼-[]-[]
≈-refl (consL x {xs} Lxs) = prf (≈-refl Lxs)
  where
    postulate prf : xs ≈ xs →  -- IH.
                    x ∷ xs ≈ x ∷ xs
    {-# ATP prove prf #-}

≡-≈ : {xs ys : D} → List xs → List ys → xs ≡ ys → xs ≈ ys
≡-≈ Lxs Lys refl = ≈-refl Lys

≈-≡ : {xs ys : D} → List xs → List ys → xs ≈ ys → xs ≡ ys
≈-≡ nilL nilL               _       = refl
≈-≡ nilL (consL y {ys} Lys) []≈y∷ys = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf #-}
≈-≡ (consL x Lxs) nilL x∷xs≈[] = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf #-}
≈-≡ (consL x {xs} Lxs) (consL y {ys} Lys) x∷xs≈y∷ys =
    ≡-list x≡y (≈-≡ Lxs Lys xs≈ys)
    where
      postulate xs≈ys : xs ≈ ys
      {-# ATP prove xs≈ys #-}

      -- The ATPs use classic logic for this proof. They should be
      -- using the transposition rule with the postulate ¬-≈ and the
      -- hypothesis x∷xs≈y∷ys. In addition it is necessary the doble
      -- negation ¬ ¬ A → A, i.e.
      --
      --     ¬ (x ≡ y) → ¬ ( x ∷ xs ≈ y ∷ ys)     x ∷ xs ≈ y ∷ ys
      -- -----------------------------------------------------------
      --                 ¬ ¬ ( x ≡ y )
      --               ------------------
      --                    x ≡ y
      postulate x≡y : x ≡ y
      {-# ATP prove x≡y #-}
