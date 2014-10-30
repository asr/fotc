{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.McCarthy91.WF-Relation.Induction.NonAcc.TerminationCheckIssue
  where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

postulate someℕ : ℕ

{-# TERMINATING #-}
foo : ℕ → ℕ → ℕ
foo n        zero    = 10
foo zero     (succ m) = foo zero someℕ
foo (succ n) (succ m) = foo n (succ m)

{-# TERMINATING #-}
bar : ℕ → ℕ → ℕ
bar n        zero    = 10
bar zero     (succ m) = bar m someℕ
bar (succ n) (succ m) = bar n (succ m)

{-# TERMINATING #-}
foobar : ℕ → ℕ → ℕ
foobar n zero = 10
foobar zero (succ m) with someℕ
... | zero   = 10
... | succ o = foobar m (succ o)
foobar (succ n) (succ m) = foobar n (succ m)
