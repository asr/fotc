------------------------------------------------------------------------------
The McCarthy 91 function: A function with nested recursion
------------------------------------------------------------------------------

In this directory we prove some properties of the McCarthy 91 function
defined by

mc91 n = if n > 100 then n - 10 else mc91 (mc91 (n + 11))

The main properties proved are:

1. The function always terminates.
2. ∀ n. n < mc91 n + 11.
3. ∀ n. n > 100 → mc91 n = n - 10.
4. ∀ n. n ≤ 100 → mc91 n = 91.
