------------------------------------------------------------------------------
-- Operations on and with functions
------------------------------------------------------------------------------

module Lib.Function where

-- The same fixity than the standard library.
infixr 0 _$_

------------------------------------------------------------------------------
-- The right associative application operator.
-- N.B. It cannot be used with types/terms which will be translated to FOL.
_$_ : ∀ {A : Set}{B : A → Set} → ((x : A) → B x) → (x : A) → B x
f $ x = f x
