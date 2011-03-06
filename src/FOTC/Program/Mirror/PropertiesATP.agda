------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

module FOTC.Program.Mirror.PropertiesATP where

open import FOTC.Base

open import FOTC.Data.List
open import FOTC.Data.List.PropertiesATP using ( reverse-[x]≡[x] )

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.ListTree.PropertiesATP
open import FOTC.Program.Mirror.ListTree.Closures
open import FOTC.Program.Mirror.Tree.ClosuresATP
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mutual
  mirror² : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
  mirror² (treeT d nilLT) = prf
    where
      postulate prf : mirror · (mirror · node d []) ≡ node d []
      {-# ATP prove prf #-}

  mirror² (treeT d (consLT {t} {ts} Tt LTts)) = prf
    where
      postulate prf : mirror · (mirror · node d (t ∷ ts)) ≡ node d (t ∷ ts)
      {-# ATP prove prf helper #-}

  helper : ∀ {ts} → ListTree ts →
           reverse (map mirror (reverse (map mirror ts))) ≡ ts
  helper nilLT = prf
    where
      postulate prf : reverse (map mirror (reverse (map mirror []))) ≡ []
      {-# ATP prove prf #-}

  helper (consLT {t} {ts} Tt LTts) =
    prf (map-++-commute mirror
                        mirror-Tree
                        (reverse-ListTree (map-ListTree mirror mirror-Tree LTts))
                        (consLT (mirror-Tree Tt) nilLT))
        (mirror² Tt)
        (helper LTts)
    where
      postulate
        -- We help the ATPs proving the first hypothesis.
        prf : (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ [])) ≡
              map mirror (reverse (map mirror ts)) ++ (map mirror (mirror · t ∷ []))) →
              mirror · (mirror · t) ≡ t →  -- IH.
              reverse (map mirror (reverse (map mirror ts))) ≡ ts →  -- IH.
              reverse (map mirror (reverse (map mirror (t ∷ ts)))) ≡ t ∷ ts
      {-# ATP prove prf reverse-∷ mirror-Tree map-ListTree reverse-++-commute
                        reverse-ListTree reverse-[x]≡[x] ++-leftIdentity #-}
