-- From Agda/examples/lib/Logic/Leibniz.agda

module Leibniz where

-- Leibniz equality
_≡_ : {A : Set} → A → A → Set1
x ≡ y = (P : _ → Set) → P x → P y

≡-refl : {A : Set}(x : A) → x ≡ x
≡-refl x P Px = Px

≡-sym : {A : Set}(x y : A) → x ≡ y → y ≡ x
≡-sym x y x≡y P Py = x≡y (λ z → P z → P x) (λ Px → Px) Py

≡-trans : {A : Set}(x y z : A) → x ≡ y → y ≡ z → x ≡ z
≡-trans x y z x≡y y≡z P Px = y≡z P (x≡y P Px)

≡-subst : {A : Set}(P : A → Set)(x y : A) → x ≡ y → P x → P y
≡-subst P _ _ x≡y = x≡y P
