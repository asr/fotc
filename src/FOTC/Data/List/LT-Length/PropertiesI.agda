------------------------------------------------------------------------------
-- Properties for the relation LTL
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.LT-Length.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI as Nat using ()
open import FOTC.Data.List
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.PropertiesI
open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

xs<[]→⊥ : ∀ {xs} → List xs → ¬ (LTL xs [])
xs<[]→⊥ Lxs xs<[] = lg-xs<lg-[]→⊥ Lxs xs<[]

x∷xs<y∷ys→xs<ys : ∀ {x xs y ys} → List xs → List ys →
                  LTL (x ∷ xs) (y ∷ ys) → LTL xs ys
x∷xs<y∷ys→xs<ys {x} {xs} {y} {ys} Lxs Lys x∷xs<y∷ys = Nat.Sx<Sy→x<y helper
  where
  helper : LT (succ₁ (length xs)) (succ₁ (length ys))
  helper =
    succ₁ (length xs) < succ₁ (length ys)
      ≡⟨ subst₂ (λ t₁ t₂ → succ₁ (length xs) < succ₁ (length ys) ≡ t₁ < t₂)
                (sym (length-∷ x xs))
                (sym (length-∷ y ys))
                refl
      ⟩
    length (x ∷ xs) < length (y ∷ ys)
      ≡⟨ x∷xs<y∷ys ⟩
    true ∎

<-trans : ∀ {xs ys zs} → List xs → List ys → List zs →
          LTL xs ys → LTL ys zs → LTL xs zs

<-trans Lxs Lys Lzs xs<ys ys<zs =
  Nat.<-trans (length-N Lxs) (length-N Lys) (length-N Lzs) xs<ys ys<zs

lg-xs≡lg-ys→ys<zx→xs<zs : ∀ {xs ys zs} → length xs ≡ length ys →
                          LTL ys zs → LTL xs zs
lg-xs≡lg-ys→ys<zx→xs<zs {xs} {ys} {zs} lg-xs≡lg-ys ys<zs =
  length xs < length zs
    ≡⟨ subst (λ t → length xs < length zs ≡ t < length zs) lg-xs≡lg-ys refl ⟩
  length ys < length zs
    ≡⟨ ys<zs ⟩
  true ∎

xs<y∷ys→xs<ys∨lg-xs≡lg-ys : ∀ {xs y ys} → List xs → List ys →
                            LTL xs (y ∷ ys) →
                            LTL xs ys ∨ length xs ≡ length ys
xs<y∷ys→xs<ys∨lg-xs≡lg-ys {xs} {y} {ys} Lxs Lys xs<y∷ys =
  Nat.x<Sy→x<y∨x≡y (length-N Lxs) (length-N Lys) helper
  where
  helper : LT (length xs) (succ₁ (length ys))
  helper =
    length xs < succ₁ (length ys)
      ≡⟨ subst (λ t → length xs < succ₁ (length ys) ≡ length xs < t)
               (sym (length-∷ y ys))
               refl
      ⟩
    length xs < length (y ∷ ys)
      ≡⟨ xs<y∷ys ⟩
    true ∎
