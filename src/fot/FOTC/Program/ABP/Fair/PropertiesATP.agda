------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair (see FOTC.Program.ABP.Fair).
Fair-pre-fixed :
  (∀ {os} → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os') →
  ∀ {os} → Fair os
Fair-pre-fixed h = Fair-coind (λ xs → xs ≡ xs) h' refl
  where
  postulate
    h' : ∀ {os} → os ≡ os → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ os' ≡ os'
  -- TODO (23 December 2013): The translation failed because we do not
  -- know how erase a term.
  -- {-# ATP prove h' #-}

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-unf Fos
... | (.(true ∷ []) , os' , f*tnil , prf , Fos') = prf₁
  where
  postulate prf₁ : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf₁ #-}

... | (.(false ∷ ft) , os' , f*tcons {ft} y , prf , Fos') = prf₁
  where
  postulate prf₁ : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf₁ #-}

-- TODO (23 December 2013).
postulate tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
