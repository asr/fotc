------------------------------------------------------------------------------
-- Operations on and with functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Function where

-- The same fixity used in the standard library.
infixr 0 _$_

------------------------------------------------------------------------------
-- The right associative application operator.
-- N.B. It cannot be used with types/terms which will be translated to FOL.
_$_ : {A : Set}{B : A → Set} → ((x : A) → B x) → (x : A) → B x
f $ x = f x

-- N.B. It cannot be used with types/terms which will be translated to FOL.
flip : {A : Set} → (A → A → A) → A → A → A
flip f y x = f x y
