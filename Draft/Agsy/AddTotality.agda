module AddTotality where

open import Relation.Binary.PropositionalEquality

infixl 9 _+_

------------------------------------------------------------------------------

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero   + d ≡ d
  +-Sx : ∀ d e → succ d + e ≡ succ (d + e)

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = {!-c -m -t 20!}  -- Agsy fails

+-N₁ : ∀ {m n} → N m → N n → N (m + n)
+-N₁ zN Nn = {!-m!}  -- Agda bug?
                     -- An internal error has occurred. Please report this as a bug.
                     -- Location of the error: src/full/Agda/Auto/Convert.hs:444

+-N₁ (sN Nm) Nn = {!-m!} -- Agda bug?
                         -- An internal error has occurred. Please report this as a bug.
                         -- Location of the error: src/full/Agda/Auto/Convert.hs:444
