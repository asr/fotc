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
  length : D → D
  length-[] : length []                     ≡ zero
  length-∷  : ( d ds : D) → length (d ∷ ds) ≡ succ (length ds)
{-# ATP axiom length-[] #-}
{-# ATP axiom length-∷ #-}

postulate
  _++_  : D → D → D
  ++-[] : (ds : D) → [] ++ ds            ≡ ds
  ++-∷  : (d ds es : D) → (d ∷ ds) ++ es ≡ d ∷ (ds ++ es)
{-# ATP axiom ++-[] #-}
{-# ATP axiom ++-∷ #-}

-- List transformations

postulate
  map    : D → D → D
  map-[] : (f : D ) → map f []           ≡ []
  map-∷  : (f d ds : D) → map f (d ∷ ds) ≡ f ∙ d ∷ map f ds
{-# ATP axiom map-[] #-}
{-# ATP axiom map-∷ #-}

postulate
  reverse    : D → D
  reverse-[] : reverse []                    ≡ []
  reverse-∷  : (d ds : D) → reverse (d ∷ ds) ≡ reverse ds ++ d ∷ []
{-# ATP axiom reverse-[] #-}
{-# ATP axiom reverse-∷ #-}

postulate
  replicate : D → D → D
  replicate-0 : (d : D) → replicate zero d       ≡ []
  replicate-S : (d e : D) → replicate (succ e) d ≡ d ∷ replicate e d
{-# ATP axiom replicate-0 #-}
{-# ATP axiom replicate-S #-}

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
