------------------------------------------------------------------------------
The Collatz function: A function without a termination proof
------------------------------------------------------------------------------

In this directory we prove some properties of the Collatz function
defined by

collatz 0          = 1
collatz 1          = 1
collatz n | even n = collatz (n / 2)
collatz n | odd n  = collatz (3n + 1)

The main property proved is: ∃ k. n = 2 ^ k → collatz n = 1.
