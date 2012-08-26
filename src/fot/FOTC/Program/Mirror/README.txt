------------------------------------------------------------------------------
The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

Given the constructor (Bove, Krauss, and Sozeua 2010)

tree : A → [ Tree A ] → Tree A

and the higher-order recursive function

mirror (tree a ts) = tree a (reverse (map mirror ts))

we prove that mirror is an involution, i.e.

mirror (mirror t) = t

• Ana Bove, Alexander Krauss, and Mattieu Sozeua. Partiality and
  recursion in interactive theorem provers. An overview. Submitted to
  publication, 2010.
