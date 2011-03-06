------------------------------------------------------------------------------
-- Properties related with the length of lists
------------------------------------------------------------------------------

module FOTC.Data.List.Length.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.Type

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

length-N : ∀ {xs} → List xs → N (length xs)
length-N nilL               = subst N (sym length-[]) zN
length-N (consL x {xs} Lxs) = subst N (sym (length-∷ x xs)) (sN (length-N Lxs))

lg-x<lg-x∷xs : ∀ x {xs} → List xs → LT (length xs) (length (x ∷ xs))
lg-x<lg-x∷xs x nilL =
  begin
    length [] < length (x ∷ [])
      ≡⟨ subst₂ (λ t₁ t₂ → length [] < length (x ∷ []) ≡ t₁ < t₂)
                length-[]
                (length-∷ x [])
                refl
      ⟩
    zero < succ (length [])
      ≡⟨ <-0S (length []) ⟩
    true
  ∎

lg-x<lg-x∷xs x (consL y {xs} Lxs) =
  begin
    length (y ∷ xs) < length (x ∷ y ∷ xs)
      ≡⟨ subst₂ (λ t₁ t₂ → length (y ∷ xs) < length (x ∷ y ∷ xs) ≡ t₁ < t₂)
                (length-∷ y xs)
                (length-∷ x (y ∷ xs))
                refl
      ⟩
    succ (length xs) < succ (length (y ∷ xs))
      ≡⟨ <-SS (length xs) (length (y ∷ xs)) ⟩
    length xs < length (y ∷ xs)
      ≡⟨ lg-x<lg-x∷xs y Lxs ⟩
    true
  ∎

lg-xs<lg-[]→⊥ : ∀ {xs} → List xs → ¬ (LT (length xs) (length []))
lg-xs<lg-[]→⊥ nilL lg-[]<lg-[] = ⊥-elim (0<0→⊥ helper)
  where
    helper : zero < zero ≡ true
    helper =
      begin
        zero < zero
          ≡⟨ subst₂ (λ t₁ t₂ → zero < zero ≡ t₁ < t₂)
                    (sym length-[])
                    (sym length-[])
                    refl
          ⟩
        length [] < length []
          ≡⟨ lg-[]<lg-[] ⟩
        true
      ∎

lg-xs<lg-[]→⊥ (consL x {xs} Lxs) lg-x∷xs<lg-[] = ⊥-elim (S<0→⊥ helper)
  where
    helper : succ (length xs) < zero ≡ true
    helper =
      begin
        succ (length xs) < zero
          ≡⟨ subst₂ (λ t₁ t₂ → succ (length xs) < zero ≡ t₁ < t₂)
                    (sym (length-∷ x xs))
                    (sym length-[])
                    refl
          ⟩
        length (x ∷ xs) < length []
          ≡⟨ lg-x∷xs<lg-[] ⟩
        true
      ∎
