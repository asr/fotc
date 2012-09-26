module FOT.FOTC.Data.Stream.Length where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Base.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream

module Version₁ where
  {-# NO_TERMINATION_CHECK #-}
  Stream-length : ∀ {xs} → Stream xs → length xs ≡ ∞
  Stream-length {xs} Sxs with (Stream-unf Sxs)
  ... | x' , xs' , Sxs' , h =
    length xs
      ≡⟨ cong length h ⟩
    length (x' ∷ xs')
      ≡⟨ lg-xs≡∞→lg-x∷xs≡∞ x' xs' (Stream-length Sxs') ⟩
    ∞ ∎

-- module Version₂ where
--   Stream-length : ∀ {xs} → Stream xs → length xs ≈N ∞
--   Stream-length xs = ≈N-coind {!!} {!!} {!!}
