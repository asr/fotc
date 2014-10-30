------------------------------------------------------------------------------
-- Well-founded relation related to the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.McCarthy91.WF-Relation where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The relation _◁_.

◁-fn : D → D
◁-fn n = 101' ∸ n
{-# ATP definition ◁-fn #-}

_◁_ : D → D → Set
m ◁ n = ◁-fn m < ◁-fn n
{-# ATP definition _◁_ #-}
