module LeibnizEquality where

------------------------------------------------------------------------------
-- The identity type
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

-- Leibniz equality (see [1, sec. 5.1.3])

-- [1] Zhaohui Luo. Computation and Reasoning. A Type Theory for
--     Computer Science. Oxford University Press, 1994.

-- (From Agda/examples/lib/Logic/Leibniz.agda)
_≐_ : {A : Set} → A → A → Set1
x ≐ y = (P : _ → Set) → P x → P y

-- Properties
≐-refl : {A : Set}{x : A} → x ≐ x
≐-refl P Px = Px

≐-sym : {A : Set}(x y : A) → x ≐ y → y ≐ x
≐-sym x y x≐y P Py = x≐y (λ z → P z → P x) (λ Px → Px) Py

≐-trans : {A : Set}{x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans x≐y y≐z P Px = y≐z P (x≐y P Px)

≐-subst : {A : Set}(P : A → Set){x y : A} → x ≐ y → P x → P y
≐-subst P x≐y = x≐y P

------------------------------------------------------------------------------
-- Leibniz's equality and the identity type

-- "In the presence of a type of propositions "Prop" one can also
-- define propositional equality by Leibniz's principle." [2, p. 4]

-- [2] Martin Hofmman. Extensional concepts in intensional type
--     theory. PhD thesis, University of Edinburgh, 1995

≐→≡ : {A : Set}{x y : A} → x ≐ y → x ≡ y
≐→≡ {x = x} x≐y = x≐y (λ z → x ≡ z) refl

≡→≐ : {A : Set}{x y : A} → x ≡ y → x ≐ y
≡→≐ refl P Px = Px
