------------------------------------------------------------------------------
The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

Given the constructor (Bove, Krauss and Sozeua 2012)

tree : A → [ Tree A ] → Tree A

and the higher-order recursive function

mirror (tree a ts) = tree a (reverse (map mirror ts))

we prove that mirror is an involution, i.e.

mirror (mirror t) = t

Bove, Ana, Krauss, Alexander and Sozeua, Mattieu (2012). Partiality
and Recursion in Interactive Theorem Provers. An Overview. Accepted
for publication at Mathematical Structures in Computer Science,
special issue on DTP 2010.
