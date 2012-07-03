-- AgdaLight code

-- # import Property

data ℕ : Set where
 zero  : ℕ
 succ  : ℕ -> ℕ

(+) : ℕ -> ℕ -> ℕ
x + zero   = x
x + succ y = succ (x + y)

comm : (x, y : ℕ ) -> x + y == y + x
comm zero     zero     = fol-plugin ()
comm zero     (succ y) = fol-plugin (comm zero y)
comm (succ x) zero     = fol-plugin (comm x zero)
comm (succ x) (succ y) = fol-plugin (comm (succ x) y
                                    , comm x y
                                    , comm x (succ y)
                                    )
