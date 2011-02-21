------------------------------------------------------------------------------
The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

Given the constructor [1]

tree : A → [ Tree A ] → Tree A

and the higher-order recursive function

mirror (tree a ts) = tree a (reverse (map mirror ts))

we prove that

mirror (mirror t) = t

[1] Ana Bove, Alexander Krauss, and Mattieu Sozeua. Partiality and
recursion in interactive theorem provers. An overview. Submitted to
publication, 2010.
