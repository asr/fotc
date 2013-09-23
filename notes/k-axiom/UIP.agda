{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

-- [1] Hofmann, Martin and Thomas Streicher (1998). “The groupoid
--     interpretation on type theory”. In: Twenty-five Years of
--     Constructive Type Theory. Ed. by Giovanni Sambin and Jan
--     M. Smith. Oxford University Press. Chap. 6.

module UIP where

data Id (A : Set)(x : A) : A → Set where
  refl : Id A x x

K : (A : Set)(x : A)(P : Id A x x → Set) → P refl → (p : Id A x x ) → P p
K A x P pr refl = pr

-- From [1, p. 88].
UIP : (A : Set)(a a' : A)(p p' : Id A a a') → Id (Id A a a') p p'
UIP A a .a refl refl = refl
