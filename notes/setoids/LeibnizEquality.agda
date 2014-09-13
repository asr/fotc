{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LeibnizEquality where

------------------------------------------------------------------------------
-- The identity type.
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

-- Leibniz equality (see [Luo 1994, sec. 5.1.3])

-- (From Agda/examples/lib/Logic/Leibniz.agda)
_≐_ : {A : Set} → A → A → Set₁
x ≐ y = (P : _ → Set) → P x → P y

-- Properties
≐-refl : {A : Set}{x : A} → x ≐ x
≐-refl P Px = Px

≐-sym : {A : Set}{x y : A} → x ≐ y → y ≐ x
≐-sym {x = x} {y} h P Py = h (λ z → P z → P x) (λ Px → Px) Py

≐-trans : {A : Set}{x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans h₁ h₂ P Px = h₂ P (h₁ P Px)

≐-subst : {A : Set}(P : A → Set){x y : A} → x ≐ y → P x → P y
≐-subst P h = h P

------------------------------------------------------------------------------
-- Leibniz's equality and the identity type

-- "In the presence of a type of propositions "Prop" one can also
-- define propositional equality by Leibniz's principle." [Hofmman
-- 1995, p. 4]

≐→≡ : {A : Set}{x y : A} → x ≐ y → x ≡ y
≐→≡ {x = x} h = h (λ z → x ≡ z) refl

≡→≐ : {A : Set}{x y : A} → x ≡ y → x ≐ y
≡→≐ refl P Px = Px

------------------------------------------------------------------------------
-- References
--
-- Hofmann, Martin (1995). Extensional concepts in intensional type
-- theory. PhD thesis. University of Edinburgh.

-- Luo, Zhaohui (1994). Computation and Reasoning. A Type Theory for
-- Computer Science. Oxford University Press.
