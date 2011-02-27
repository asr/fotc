module TerminationCheckIssue where

open import Data.Nat

postulate
  someℕ : ℕ

foo : ℕ → ℕ → ℕ
foo m       zero    = 10
foo zero    (suc n) = foo zero someℕ
foo (suc m) (suc n) = foo m (suc n)

bar : ℕ → ℕ → ℕ
bar m       zero    = 10
bar zero    (suc n) = bar n someℕ
bar (suc m) (suc n) = bar m (suc n)

foobar : ℕ → ℕ → ℕ
foobar m zero = 10
foobar zero (suc n) with someℕ
... | zero  = 10
... | suc o = foobar n (suc o)
foobar (suc m) (suc n) = foobar m (suc n)
