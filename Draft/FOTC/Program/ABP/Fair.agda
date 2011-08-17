------------------------------------------------------------------------------
-- Fairness of the ABP channels
------------------------------------------------------------------------------

module Draft.FOTC.Program.ABP.Fair where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Relation.Binary.EqReasoning

open import Draft.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- The Fair co-inductive predicate

-- From the paper: al : O*L if al is a list of zero or more O's
-- followed by a final L.
data O*L : D → Set where
  nilO*L  :                 O*L (L ∷ [])
  consO*L : ∀ ol → O*L ol → O*L (O ∷ ol)

-- Functor for the Fair type.
-- FairF : (D → Set) → D → Set
-- FairF X os = ∃ λ ol → ∃ λ os' → O*L ol ∧ X os' ∧ os ≡ ol ++ os'

postulate Fair : D → Set

-- Fair is post-fixed point of FairF (d ≤ f d).
postulate
  Fair-gfp₁ : ∀ {os} → Fair os →
              ∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os'

-- Fair is the greatest post-fixed of FairF.
--
-- (If ∀ e. e ≤ f e => e ≤ d, then d is the greatest post-fixed point
-- of f).
postulate
  Fair-gfp₂ : (P : D → Set) →
              -- P is post-fixed point of FairF.
              ( ∀ {os} → P os →
                ∃ λ ol → ∃ λ os' → O*L ol ∧ P os' ∧ os ≡ ol ++ os' ) →
              -- Fair is greater than P.
              ∀ {os} → P os → Fair os

-- Because a greatest post-fixed point is a fixed point, then the Fair
-- predicate is also a pre-fixed point of the functor FairF (f d ≤ d).
Fair-gfp₃ : ∀ {os} →
            (∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os') →
            Fair os
Fair-gfp₃ h = Fair-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃ λ wl → ∃ λ ws' → O*L wl ∧ Fair ws' ∧ ws ≡ wl ++ ws'

  helper : {os : D} → P os → ∃ λ ol → ∃ λ os' → O*L ol ∧ P os' ∧ os ≡ ol ++ os'
  helper (ol , os' , OLol , Fos' , h) = ol , os' , OLol , Fair-gfp₁ Fos' , h

------------------------------------------------------------------------------
-- Properties

head-tail-Fair-helper : ∀ {os ol os'} → O*L ol → os ≡ ol ++ os' →
                        os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
head-tail-Fair-helper {os} {os' = os'} nilO*L h = inj₁ prf₃
  where
  prf₁ : os ≡ L ∷ [] ++ os'
  prf₁ =
    begin
      os              ≡⟨ h ⟩
      (L ∷ []) ++ os' ≡⟨ ++-∷ L [] os' ⟩
      L ∷ [] ++ os'
    ∎

  prf₂ : tail os ≡ [] ++ os'
  prf₂ =
    begin
      tail os              ≡⟨ cong tail prf₁ ⟩
      tail (L ∷ [] ++ os') ≡⟨ tail-∷ L ([] ++ os') ⟩
      [] ++ os'
    ∎

  prf₃ : os ≡ L ∷ tail os
  prf₃ =
    begin
      os             ≡⟨ prf₁ ⟩
      L ∷ [] ++ os'  ≡⟨ cong (_∷_ L) (sym prf₂) ⟩
      L ∷ tail os
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

  prf₂ : tail os ≡ ol ++ os'
  prf₂ =
    begin
      tail os              ≡⟨ cong tail prf₁ ⟩
      tail (O ∷ ol ++ os') ≡⟨ tail-∷ O (ol ++ os') ⟩
      ol ++ os'
    ∎

  prf₃ : os ≡ O ∷ tail os
  prf₃ =
    begin
      os             ≡⟨ prf₁ ⟩
      O ∷ ol ++ os'  ≡⟨ cong (_∷_ O) (sym prf₂) ⟩
      O ∷ tail os
    ∎

head-tail-Fair : ∀ {os} → Fair os → os ≡ L ∷ tail os ∨ os ≡ O ∷ tail os
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
                   Fair (tail os)
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

  prf₂ : tail os ≡ os'
  prf₂ =
    begin
      tail os        ≡⟨ cong tail prf₁ ⟩
      tail (L ∷ os') ≡⟨ tail-∷ L os' ⟩
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

  prf₂ : tail os ≡ ol ++ os'
  prf₂ =
    begin
      tail os              ≡⟨ cong tail prf₁ ⟩
      tail (O ∷ ol ++ os') ≡⟨ tail-∷ O (ol ++ os') ⟩
      ol ++ os'
    ∎

tail-Fair : ∀ {os} → Fair os → Fair (tail os)
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
