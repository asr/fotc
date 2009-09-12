module Add where

infixl 60 _+_
infix  30 _==_

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

postulate
 _==_ : ℕ -> ℕ -> Set

_+_ : ℕ -> ℕ -> ℕ
x + zero   = x
x + succ y = succ (x + y)

postulate
 idLeft+0  : zero + zero == zero
 -- idLeft+IS1 : (x : ℕ) -> zero + x == x -> zero + succ x == succ x
 idLeft+IS2 : (x : ℕ) -> zero + x == x -> succ (zero + x) == succ x

idLeft+ : (x : ℕ) -> zero + x == x
idLeft+ zero     = idLeft+0
idLeft+ (succ x) = idLeft+IS2 x (idLeft+ x)

{-# EXTERNAL Equinox idLeft+0 #-}
{-# EXTERNAL Equinox idLeft+IS2 #-}
