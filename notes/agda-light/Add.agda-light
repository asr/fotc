-- AgdaLight code

-- # import Property

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

(+) : Nat -> Nat -> Nat
x + zero  = x
x + suc y = suc (x + y)

idLeft+ : (x : Nat) -> zero + x == x
idLeft+ zero    = fol-plugin ()
idLeft+ (suc x) = fol-plugin (idLeft+ x)

{-
comm+ : (x, y : Nat ) -> x + y == y + x
comm+ zero zero       = fol-plugin ()
comm+ zero (suc y)    = fol-plugin (comm+ zero y)
comm+ zero (suc y)    = fol-plugin ()
comm+ (suc x) zero    = fol-plugin (comm+ x zero)
comm+ (suc x) (suc y) = fol-plugin (comm+ (suc x) y
                                   , comm+ x y
                                   , comm+ x (suc y)
                                   )
-}
