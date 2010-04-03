module Logic where

infix  30 _≡_

postulate
  D    : Set
  _≡_ : D → D → Set

import LogicalConstants
open module LC = LogicalConstants D

postulate
 f10 : (A : Set)   → A Implies A
 f20 : (A B : Set) → A And B Implies B And A
 f30 : (A : Set)   → Not (A And True) Equiv (Not A Or False)
 f40 : (d : D)     → d ≡ d
 f50 : (d1 d2 : D) → (d1 ≡ d2) Implies (d2 ≡ d1)

 f60 : ForAll (λ (x : D) → x ≡ x)
 f70 : (x : D) → x ≡ x
 f80 : ForAll (λ (x : D) → Exists ( λ (y : D) → x ≡ y))

{-# EXTERNAL axiom f10 #-}
{-# EXTERNAL axiom f20 #-}
{-# EXTERNAL axiom f30 #-}
{-# EXTERNAL axiom f40 #-}
{-# EXTERNAL axiom f50 #-}
{-# EXTERNAL axiom f60 #-}
{-# EXTERNAL axiom f70 #-}
{-# EXTERNAL axiom f80 #-}
