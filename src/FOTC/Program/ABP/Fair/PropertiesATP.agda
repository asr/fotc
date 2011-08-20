------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {os ol os'} → O*L ol → os ≡ ol ++ os' →
                        os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
head-tail-Fair-helper {os} {os' = os'} nilO*L h = prf
  where
  postulate prf : os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
  {-# ATP prove prf #-}

head-tail-Fair-helper {os} {os' = os'} (consO*L ol OLol) h = prf
  where
  postulate prf : os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
  {-# ATP prove prf #-}

head-tail-Fair : ∀ {os} → Fair os → os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
head-tail-Fair {os} Fos = prf
  where
  postulate prf : os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
  {-# ATP prove prf head-tail-Fair-helper #-}

tail-Fair-helper : ∀ {os ol os'} → O*L ol → os ≡ ol ++ os' → Fair os' →
                   Fair (tail os)
tail-Fair-helper {os} {os' = os'} nilO*L h Fos' = prf
  where
  postulate prf : Fair (tail os)
  {-# ATP prove prf #-}

tail-Fair-helper {os} {os' = os'} (consO*L ol OLol) h Fos' = prf
  where
  postulate prf : Fair (tail os)
  {-# ATP prove prf Fair-gfp₃ #-}

tail-Fair : ∀ {os} → Fair os → Fair (tail os)
tail-Fair {os} Fos = prf
  where
  postulate prf : Fair (tail os)
  {-# ATP prove prf tail-Fair-helper #-}
