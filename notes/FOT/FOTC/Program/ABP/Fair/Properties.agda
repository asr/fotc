------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.ABP.Fair.Properties where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Stream.Type
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

Fair→Stream : ∀ {os} → Fair os → Stream os
Fair→Stream {os} Fos = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs

  h : A os → ∃[ o' ] ∃[ os' ] os ≡ o' ∷ os' ∧ A os'
  h _ with head-tail-Fair Fos
  h x₁ | inj₁ prf = T , tail₁ os , prf , refl
  h x₁ | inj₂ prf = F , tail₁ os , prf , refl

F*T→List : ∀ {xs} → F*T xs → List xs
F*T→List f*tnil              = lcons true lnil
F*T→List (f*tcons {ft} FTft) = lcons false (F*T→List FTft)
