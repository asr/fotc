------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Mirror.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesATP using ( reverse-[x]≡[x] )
open import FOTC.Program.Mirror.Forest.PropertiesATP
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Tree.TotalityATP
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-involutive : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
helper            : ∀ {ts} → Forest ts →
                    reverse (map mirror (reverse (map mirror ts))) ≡ ts

mirror-involutive (tree d fnil) = prf
  where postulate prf : mirror · (mirror · node d []) ≡ node d []
        {-# ATP prove prf #-}

mirror-involutive (tree d (fcons {t} {ts} Tt Fts)) = prf
  where postulate prf : mirror · (mirror · node d (t ∷ ts)) ≡ node d (t ∷ ts)
        {-# ATP prove prf helper #-}

helper fnil = prf
  where postulate prf : reverse (map mirror (reverse (map mirror []))) ≡ []
        {-# ATP prove prf #-}

helper (fcons {t} {ts} Tt Fts) =
  prf (map-++ mirror
              mirror-Tree
              (reverse-Forest (map-Forest mirror mirror-Tree Fts))
              (mirror · t ∷ []))
      (mirror-involutive Tt)
      (helper Fts)
  where
  postulate
    -- We help the ATPs proving the first hypothesis.
    prf : (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ [])) ≡
          map mirror
              (reverse (map mirror ts)) ++ (map mirror (mirror · t ∷ []))) →
          mirror · (mirror · t) ≡ t →
          reverse (map mirror (reverse (map mirror ts))) ≡ ts →
          reverse (map mirror (reverse (map mirror (t ∷ ts)))) ≡ t ∷ ts
  {-# ATP prove prf reverse-∷ mirror-Tree map-Forest reverse-++
                    reverse-Forest reverse-[x]≡[x] #-}
