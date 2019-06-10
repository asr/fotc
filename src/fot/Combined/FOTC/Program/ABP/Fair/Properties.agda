------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.ABP.Fair.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.List
open import Combined.FOTC.Program.ABP.Fair.Type
open import Combined.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair (see Combined.FOTC.Program.ABP.Fair).

-- See Issue https://github.com/asr/apia/issues/81 .
Fair-inA : D → Set
Fair-inA os = ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os'
{-# ATP definition Fair-inA #-}

Fair-in : ∀ {os} → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os' →
          Fair os
Fair-in h = Fair-coind Fair-inA h' h
  where
  postulate
    h' : ∀ {os} → Fair-inA os →
         ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair-inA os'
  {-# ATP prove h' #-}

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-out Fos
... | (.(T ∷ []) , os' , f*tnil , h , Fos') = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

... | (.(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos') = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos with Fair-out Fos
... | .(T ∷ []) , os' , f*tnil , h , Fos' = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf #-}
... | .(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos' = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf Fair-in #-}
