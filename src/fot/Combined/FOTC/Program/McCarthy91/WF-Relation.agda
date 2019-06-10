------------------------------------------------------------------------------
-- Well-founded relation related to the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.McCarthy91.WF-Relation where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The relation _◁_.

◁-fn : D → D
◁-fn n = 101' ∸ n
{-# ATP definition ◁-fn #-}

_◁_ : D → D → Set
m ◁ n = ◁-fn m < ◁-fn n
{-# ATP definition _◁_ #-}
