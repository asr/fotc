------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

module FOTC.Program.ABP.Fair.PropertiesI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Relation.Binary.EqReasoning
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {os ol os'} → O*L ol → os ≡ ol ++ os' →
                        os ≡ L ∷ tail₁ os ∨ os ≡ O ∷ tail₁ os
head-tail-Fair-helper {os} {os' = os'} nilO*L h = inj₁ prf₃
  where
  prf₁ : os ≡ L ∷ [] ++ os'
  prf₁ =
    begin
      os              ≡⟨ h ⟩
      (L ∷ []) ++ os' ≡⟨ ++-∷ L [] os' ⟩
      L ∷ [] ++ os'
    ∎

  prf₂ : tail₁ os ≡ [] ++ os'
  prf₂ =
    begin
      tail₁ os              ≡⟨ cong tail₁ prf₁ ⟩
      tail₁ (L ∷ [] ++ os') ≡⟨ tail-∷ L ([] ++ os') ⟩
      [] ++ os'
    ∎

  prf₃ : os ≡ L ∷ tail₁ os
  prf₃ =
    begin
      os             ≡⟨ prf₁ ⟩
      L ∷ [] ++ os'  ≡⟨ cong (_∷_ L) (sym prf₂) ⟩
      L ∷ tail₁ os
    ∎

head-tail-Fair-helper {os} {os' = os'} (consO*L ol OLol) h = inj₂ prf₃
  where
  prf₁ : os ≡ O ∷ ol ++ os'
  prf₁ =
    begin
      os              ≡⟨ h ⟩
      (O ∷ ol) ++ os' ≡⟨ ++-∷ O ol os' ⟩
      O ∷ ol ++ os'
    ∎

  prf₂ : tail₁ os ≡ ol ++ os'
  prf₂ =
    begin
      tail₁ os              ≡⟨ cong tail₁ prf₁ ⟩
      tail₁ (O ∷ ol ++ os') ≡⟨ tail-∷ O (ol ++ os') ⟩
      ol ++ os'
    ∎

  prf₃ : os ≡ O ∷ tail₁ os
  prf₃ =
    begin
      os             ≡⟨ prf₁ ⟩
      O ∷ ol ++ os'  ≡⟨ cong (_∷_ O) (sym prf₂) ⟩
      O ∷ tail₁ os
    ∎

head-tail-Fair : ∀ {os} → Fair os → os ≡ L ∷ tail₁ os ∨ os ≡ O ∷ tail₁ os
head-tail-Fair {os} Fos = head-tail-Fair-helper OLol os≡ol++os'
  where
  unfold-os : ∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os'
  unfold-os = Fair-gfp₁ Fos

  ol : D
  ol = ∃-proj₁ unfold-os

  os' : D
  os' = ∃-proj₁ (∃-proj₂ unfold-os)

  OLol : O*L ol
  OLol = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os))

  os≡ol++os' : os ≡ ol ++ os'
  os≡ol++os' = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os)))

tail-Fair-helper : ∀ {os ol os'} → O*L ol → os ≡ ol ++ os' → Fair os' →
                   Fair (tail₁ os)
tail-Fair-helper {os} {os' = os'} nilO*L h Fos' = subst Fair (sym prf₂) Fos'
  where
  prf₁ : os ≡ L ∷ os'
  prf₁ =
    begin
      os              ≡⟨ h ⟩
      (L ∷ []) ++ os' ≡⟨ ++-∷ L [] os' ⟩
      L ∷ [] ++ os'   ≡⟨ cong (_∷_ L) (++-[] os') ⟩
      L ∷ os'
    ∎

  prf₂ : tail₁ os ≡ os'
  prf₂ =
    begin
      tail₁ os        ≡⟨ cong tail₁ prf₁ ⟩
      tail₁ (L ∷ os') ≡⟨ tail-∷ L os' ⟩
      os'
    ∎

tail-Fair-helper {os} {os' = os'} (consO*L ol OLol) h Fos' =
  subst Fair (sym prf₂) (Fair-gfp₃ (ol , os' , OLol , Fos' , refl))
  where
  prf₁ : os ≡ O ∷ ol ++ os'
  prf₁ =
    begin
      os              ≡⟨ h ⟩
      (O ∷ ol) ++ os' ≡⟨ ++-∷ O ol os' ⟩
      O ∷ ol ++ os'
    ∎

  prf₂ : tail₁ os ≡ ol ++ os'
  prf₂ =
    begin
      tail₁ os              ≡⟨ cong tail₁ prf₁ ⟩
      tail₁ (O ∷ ol ++ os') ≡⟨ tail-∷ O (ol ++ os') ⟩
      ol ++ os'
    ∎

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos = tail-Fair-helper OLol os≡ol++os' Fos'
  where
  unfold-os : ∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os'
  unfold-os = Fair-gfp₁ Fos

  ol : D
  ol = ∃-proj₁ unfold-os

  os' : D
  os' = ∃-proj₁ (∃-proj₂ unfold-os)

  OLol : O*L ol
  OLol = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os))

  Fos' : Fair os'
  Fos' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os)))

  os≡ol++os' : os ≡ ol ++ os'
  os≡ol++os' = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os)))
