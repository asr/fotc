{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}  -- No accepted!

-- Using a non-strictly positive type is possible to get a
-- contradiction. From Coq' Art, section 14.1.2.1.

module FalseProof where

open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary

n≠Sn : ∀ {n} → ¬ (n ≡ suc n)
n≠Sn ()

data T : Set where
  l : (T → T) → T

abstract
  depth : T → ℕ
  depth (l f) = suc (depth (f (l f)))

  depth-thm : {f : T → T} → depth (l f) ≡ suc (depth (f (l f)))
  depth-thm = refl


-- Then:
--
-- depth (l (λ t → t)) =
-- suc (depth ((λ t → t) (l (λ t → t)))) =
-- suc (depth (l (λ t → t)))

-- which contradicts the theorem n≠Sn.


thm : depth (l (λ t → t)) ≡ suc (depth (l (λ t → t)))
thm =
    begin
      depth (l (λ t → t))
    ≡⟨ depth-thm ⟩
      suc (depth ((λ t → t) (l (λ t → t))))
    ≡⟨ refl ⟩
      suc (depth (l (λ t → t)))
    ∎

bottom : ⊥
bottom = n≠Sn thm
