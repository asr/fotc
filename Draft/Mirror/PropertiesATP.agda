------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check  #-}

module Draft.Mirror.PropertiesATP where

open import LTC.Base

open import Draft.Mirror.Mirror
open import Draft.Mirror.ListTree.PropertiesATP
open import Draft.Mirror.ListTree.Closures

open import LTC.Data.List
open import LTC.Data.List.PropertiesATP using ( reverse-[x]≡[x] )
open import Draft.Mirror.ListTree.PropertiesATP

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- TODO: To remove
postulate
  mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)

mirror² : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
mirror² (treeT d nilLT) = prf
  where
    postulate prf : mirror · (mirror · node d []) ≡ node d []
    {-# ATP prove prf #-}

mirror² (treeT d (consLT {t} {ts} Tt LTts)) =
  prf (mirror² Tt) (mirror² (treeT d LTts))
  where
    postulate prf : mirror · (mirror · t) ≡ t → -- IH.
                    mirror · (mirror · node d ts) ≡ node d ts → -- IH.
                    mirror · (mirror · node d (t ∷ ts)) ≡ node d (t ∷ ts)
    {-# ATP prove prf reverse-∷ map-ListTree mirror-Tree map-++-commute
                      reverse-++-commute rev-ListTree reverse-[x]≡[x]
                      ++-leftIdentity
    #-}
