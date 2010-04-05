module LogicalConstants (D : Set) where

infix  80 Not
infixl 70 _And_
infixl 60 _Or_
infixl 50 _Implies_
infixl 40 _Equiv_

postulate
  True False                   : Set
  Not                          : Set → Set
  _And_ _Implies_ _Or_ _Equiv_ : Set → Set → Set

  Exists ForAll : (D → Set) → Set
