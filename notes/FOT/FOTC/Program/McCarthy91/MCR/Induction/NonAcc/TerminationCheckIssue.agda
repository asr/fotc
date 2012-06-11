module TerminationCheckIssue where

open import Data.Nat

postulate
  someℕ : ℕ

foo : ℕ → ℕ → ℕ
foo n       zero    = 10
foo zero    (suc m) = foo zero someℕ
foo (suc n) (suc m) = foo n (suc m)

bar : ℕ → ℕ → ℕ
bar n       zero    = 10
bar zero    (suc m) = bar m someℕ
bar (suc n) (suc m) = bar n (suc m)

foobar : ℕ → ℕ → ℕ
foobar n zero = 10
foobar zero (suc m) with someℕ
... | zero  = 10
... | suc o = foobar m (suc o)
foobar (suc n) (suc m) = foobar n (suc m)
