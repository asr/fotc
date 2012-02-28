------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {fs} →
                        ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                        fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair-helper {fs} (∃-intro (∃-intro (nilF*T , h₁ , h₂))) = prf
  where
  postulate prf : fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
  {-# ATP prove prf #-}

head-tail-Fair-helper {fs} (∃-intro (∃-intro (consF*T y , h₁ , h₂))) = prf
  where
  postulate prf : fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
  {-# ATP prove prf #-}

head-tail-Fair : ∀ {fs} → Fair fs → fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair {fs} Ffs = prf
  where
  postulate prf : fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
  {-# ATP prove prf head-tail-Fair-helper #-}

tail-Fair-helper : ∀ {fs} →
                   ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                   Fair (tail₁ fs)
tail-Fair-helper {fs} (∃-intro (∃-intro (nilF*T , Ffs' , h))) = prf
  where
  postulate prf : Fair (tail₁ fs)
  {-# ATP prove prf #-}

tail-Fair-helper {fs} (∃-intro (∃-intro (consF*T FTft , Ffs' , h))) = prf
  where
  postulate prf : Fair (tail₁ fs)
  {-# ATP prove prf Fair-gfp₃ #-}

tail-Fair : ∀ {fs} → Fair fs → Fair (tail₁ fs)
tail-Fair {fs} Ffs = prf
  where
  postulate prf : Fair (tail₁ fs)
  {-# ATP prove prf tail-Fair-helper #-}
