------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

module LTC.Data.List where

open import LTC.Minimal

------------------------------------------------------------------------------

infixr 5 _∷_ _++_

-- List terms
postulate
  []   : D
  _∷_  : D → D → D

-- Basic functions
postulate
  head : D → D
  cHead : (d ds : D) → head (d ∷ ds) ≡ d

postulate
  tail : D → D
  cTail : (d ds : D) → tail (d ∷ ds) ≡ ds

postulate
  _++_  : D → D → D
  ++-[] : (ds : D) → [] ++ ds            ≡ ds
  ++-∷  : (d ds es : D) → (d ∷ ds) ++ es ≡ d ∷ (ds ++ es)
{-# ATP axiom ++-[] #-}
{-# ATP axiom ++-∷ #-}

postulate
  reverse    : D → D
  reverse-[] : reverse []                    ≡ []
  reverse-∷  : (d ds : D) → reverse (d ∷ ds) ≡ reverse ds ++ d ∷ []
{-# ATP axiom reverse-[] #-}
{-# ATP axiom reverse-∷ #-}

postulate
  map    : D → D → D
  map-[] : (f : D ) → map f []           ≡ []
  map-∷  : (f d ds : D) → map f (d ∷ ds) ≡ f ∙ d ∷ map f ds
{-# ATP axiom map-[] #-}
{-# ATP axiom map-∷ #-}

------------------------------------------------------------------------------

-- The LTC list data type
data List : D → Set where
  nil  : List []
  cons : (d : D){ds : D} → (dsL : List ds) → List (d ∷ ds)

-- Induction principle for List
indList : (P : D → Set) →
          P [] →
          ((d : D){ds : D} → List ds → P ds → P (d ∷ ds)) →
          {ds : D} → List ds → P ds
indList P p[] iStep nil               = p[]
indList P p[] iStep (cons d {ds} dsL) = iStep d dsL (indList P p[] iStep dsL)
