------------------------------------------------------------------------------
-- Well-founded induction
------------------------------------------------------------------------------

module MyStdLib.Induction.WellFounded where

-- From: http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/

data Acc {A : Set}(R : A → A → Set) : A → Set where
  acc : (x : A) → (( y : A) →  R y x → Acc R y) → Acc R x

WellFound : {A : Set} → (A → A → Set) → Set
WellFound {A} R = (x : A) → Acc R x

accFold : {A : Set}(R : A → A → Set){P : A → Set} →
          ((x : A) → ((y : A) → R y x → P y) → P x) →
          (x : A) → Acc R x → P x
accFold R f x (acc .x h) = f x (λ y y<x → accFold R f y (h y y<x))

wfInd : {A : Set} {R : A → A → Set} {P : A → Set} →
        WellFound R →
        ((x : A) → ((y : A) → R y x → P y) → P x) →
        (x : A) → P x
wfInd {R = R} wf f x = accFold R f x (wf x)
