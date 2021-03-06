------------------------------------------------------------------------------
-- Operations on and with functions
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Common.Function where

-- From Funcion.agda (Agda standard library 0.8.1).
-- infixr 0 _$_

------------------------------------------------------------------------------
-- The right associative application operator.
--
-- N.B. The operator is not first-order, so it cannot be used with
-- types/terms which will be translated to FOL.
-- _$_ : {A : Set}{B : A → Set} → ((x : A) → B x) → (x : A) → B x
-- f $ x = f x

-- N.B. The function is not first-order, so it cannot be used with
-- types/terms which will be translated to FOL.
-- flip : {A : Set} → (A → A → A) → A → A → A
-- flip f y x = f x y
