------------------------------------------------------------------------------
-- Well-founded induction
------------------------------------------------------------------------------

module MyStdLib.Induction.WellFounded where

------------------------------------------------------------------------------
-- Well-founded induction on an order relation R : A → A → A → A → Set
-- TODO: Is it possible to define these functions using the previous one?

data Acc₂ {A : Set}(R : A → A → A → A → Set) : A → A → Set where
  acc₂ : {x₁ y₁ : A} → ({x₂ y₂ : A} → R x₂ y₂ x₁ y₁ → Acc₂ R x₂ y₂) →
         Acc₂ R x₁ y₁

WellFounded₂ : {A : Set} → (A → A → A → A → Set) → Set
WellFounded₂ {A} R = (x y : A) → Acc₂ R x y

accFold₂ : {A : Set}(R : A → A → A → A → Set){P : A → A → Set} →
          ({x₁ y₁ : A} → ({x₂ y₂ : A} → R x₂ y₂ x₁ y₁ → P x₂ y₂) → P x₁ y₁) →
          {x y : A} → Acc₂ R x y → P x y
accFold₂ R f {x₁} {y₁} (acc₂ h) = f (λ x₂y₂<x₁y₁ → accFold₂ R f (h x₂y₂<x₁y₁))

wfInd₂ : {A : Set} {R : A → A → A → A → Set} {P : A → A → Set} →
         WellFounded₂ R →
         ({x₁ y₁ : A} → ({x₂ y₂ : A} → R x₂ y₂ x₁ y₁ → P x₂ y₂ ) → P x₁ y₁) →
         {x y : A} → P x y
wfInd₂ {R = R} wf f {x} {y} = accFold₂ R f (wf x y)
