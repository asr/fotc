------------------------------------------------------------------------------
-- Properties for the relation LTL
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.List.WF-Relation.LT-Length.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.Properties as Nat using ()
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------

xs<[]→⊥ : ∀ {xs} → List xs → ¬ (LTL xs [])
xs<[]→⊥ Lxs xs<[] = lg-xs<lg-[]→⊥ Lxs xs<[]

x∷xs<y∷ys→xs<ys : ∀ {x xs y ys} → List xs → List ys →
                  LTL (x ∷ xs) (y ∷ ys) → LTL xs ys
x∷xs<y∷ys→xs<ys {x} {xs} {y} {ys} Lxs Lys x∷xs<y∷ys = Nat.Sx<Sy→x<y helper
  where
  helper : succ₁ (length xs) < succ₁ (length ys)
  helper =
    lt (succ₁ (length xs)) (succ₁ (length ys))
      ≡⟨ subst₂ (λ t t' → lt (succ₁ (length xs)) (succ₁ (length ys)) ≡ lt t t')
                (sym (length-∷ x xs))
                (sym (length-∷ y ys))
                refl
      ⟩
    lt (length (x ∷ xs)) (length (y ∷ ys))
      ≡⟨ x∷xs<y∷ys ⟩
    true ∎

<-trans : ∀ {xs ys zs} → List xs → List ys → List zs →
          LTL xs ys → LTL ys zs → LTL xs zs

<-trans Lxs Lys Lzs xs<ys ys<zs =
  Nat.<-trans (lengthList-N Lxs) (lengthList-N Lys) (lengthList-N Lzs) xs<ys ys<zs

lg-xs≡lg-ys→ys<zx→xs<zs : ∀ {xs ys zs} → length xs ≡ length ys →
                          LTL ys zs → LTL xs zs
lg-xs≡lg-ys→ys<zx→xs<zs {xs} {ys} {zs} h ys<zs =
  lt (length xs) (length zs)
    ≡⟨ subst (λ t → lt (length xs) (length zs) ≡ lt t (length zs)) h refl ⟩
  lt (length ys) (length zs)
    ≡⟨ ys<zs ⟩
  true ∎

xs<y∷ys→xs<ys∨lg-xs≡lg-ys : ∀ {xs y ys} → List xs → List ys →
                            LTL xs (y ∷ ys) →
                            LTL xs ys ∨ length xs ≡ length ys
xs<y∷ys→xs<ys∨lg-xs≡lg-ys {xs} {y} {ys} Lxs Lys xs<y∷ys =
  Nat.x<Sy→x<y∨x≡y (lengthList-N Lxs) (lengthList-N Lys) helper
  where
  helper : length xs < succ₁ (length ys)
  helper =
    lt (length xs) (succ₁ (length ys))
      ≡⟨ subst (λ t → lt (length xs) (succ₁ (length ys)) ≡ lt (length xs) t)
               (sym (length-∷ y ys))
               refl
      ⟩
    lt (length xs) (length (y ∷ ys))
      ≡⟨ xs<y∷ys ⟩
    true ∎
