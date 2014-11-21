{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PolynomialFunctors where

-- From: Ulf Norell. Dependently typed programming in Agda. In Koopman
-- et al., editors. Advanced Functional Programming (AFP 2008), volume
-- 5832 of LNCS. Springer-Verlag, 2009. pages 230–266.

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _×_

record True : Set where

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Functor : Set₁ where
  |Id|  : Functor
  |K|   : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|x|_ : Functor → Functor → Functor

[_] : Functor → Set → Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) → μ F

NatF : Functor
NatF = |K| True |+| |Id|

NAT : Set
NAT = μ NatF

Z : NAT
Z = < inl _ >

S : NAT → NAT
S n = < inr n >

_+_ : NAT → NAT → NAT
m + < inl _ > = m
m + < inr n > = S (m + n)

ListF : (A : Set) → Functor
ListF = λ A → |K| True |+| |K| A |x| |Id|

LIST : (A : Set) → Set
LIST = λ A → μ (ListF A)

nil : {A : Set} → LIST A
nil = < inl _ >

cons : {A : Set} → A → LIST A → LIST A
cons x xs = < inr (x , xs) >
