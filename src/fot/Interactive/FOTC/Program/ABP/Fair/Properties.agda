------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.ABP.Fair.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.Stream.Type
open import Interactive.FOTC.Program.ABP.Fair.Type
open import Interactive.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair (see Interactive.FOTC.Program.ABP.Fair).
Fair-in : ∀ {os} → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os' →
          Fair os
Fair-in h = Fair-coind A h' h
  where
  A : D → Set
  A os = ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os'

  h' : ∀ {os} → A os → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ A os'
  h' (ft , os' , FTft , prf , Fos') = ft , os' , FTft , prf , Fair-out Fos'

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-out Fos
... | .(T ∷ []) , os' , f*tnil , h , Fos' = inj₁ prf₃
  where
  prf₁ : os ≡ T ∷ [] ++ os'
  prf₁ = os              ≡⟨ h ⟩
         (T ∷ []) ++ os' ≡⟨ ++-∷ T [] os' ⟩
         T ∷ [] ++ os'   ∎

  prf₂ : tail₁ os ≡ [] ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (T ∷ [] ++ os') ≡⟨ tail-∷ T ([] ++ os') ⟩
         [] ++ os'             ∎

  prf₃ : os ≡ T ∷ tail₁ os
  prf₃ = os             ≡⟨ prf₁ ⟩
         T ∷ [] ++ os'  ≡⟨ ∷-rightCong (sym prf₂) ⟩
         T ∷ tail₁ os   ∎

... | .(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos' =
  inj₂ prf₃
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ h ⟩
         (F ∷ ft) ++ os' ≡⟨ ++-∷ F ft os' ⟩
         F ∷ ft ++ os'   ∎

  prf₂ : tail₁ os ≡ ft ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (F ∷ ft ++ os') ≡⟨ tail-∷ F (ft ++ os') ⟩
         ft ++ os'             ∎

  prf₃ : os ≡ F ∷ tail₁ os
  prf₃ = os             ≡⟨ prf₁ ⟩
         F ∷ ft ++ os'  ≡⟨ ∷-rightCong (sym prf₂) ⟩
         F ∷ tail₁ os   ∎

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos with Fair-out Fos
... | .(T ∷ []) , os' , f*tnil , h , Fos' =
  subst Fair (sym prf₂) Fos'
  where
  prf₁ : os ≡ T ∷ os'
  prf₁ = os              ≡⟨ h ⟩
         (T ∷ []) ++ os' ≡⟨ ++-∷ T [] os' ⟩
         T ∷ [] ++ os'   ≡⟨ ∷-rightCong (++-leftIdentity os') ⟩
         T ∷ os'         ∎

  prf₂ : tail₁ os ≡ os'
  prf₂ = tail₁ os        ≡⟨ tailCong prf₁ ⟩
         tail₁ (T ∷ os') ≡⟨ tail-∷ T os' ⟩
         os'             ∎

... | .(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos' =
    subst Fair (sym prf₂) (Fair-in (ft , os' , FTft , refl , Fos'))
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ h ⟩
         (F ∷ ft) ++ os' ≡⟨ ++-∷ F ft os' ⟩
         F ∷ ft ++ os'   ∎

  prf₂ : tail₁ os ≡ ft ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (F ∷ ft ++ os') ≡⟨ tail-∷ F (ft ++ os') ⟩
         ft ++ os'             ∎

Fair→Stream : ∀ {os} → Fair os → Stream os
Fair→Stream Fos = Stream-coind A h Fos
  where
  A : D → Set
  A xs = Fair xs

  h : ∀ {os} → A os → ∃[ o' ] ∃[ os' ] os ≡ o' ∷ os' ∧ A os'
  h {os} As with head-tail-Fair As
  ... | inj₁ prf = T , tail₁ os , prf , tail-Fair As
  ... | inj₂ prf = F , tail₁ os , prf , tail-Fair As

F*T→List : ∀ {xs} → F*T xs → List xs
F*T→List f*tnil              = lcons T lnil
F*T→List (f*tcons {ft} FTft) = lcons F (F*T→List FTft)
