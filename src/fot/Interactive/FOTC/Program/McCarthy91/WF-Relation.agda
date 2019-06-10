------------------------------------------------------------------------------
-- Well-founded relation related to the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.McCarthy91.WF-Relation where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The relation _◁_.

◁-fn : D → D
◁-fn n = 101' ∸ n

_◁_ : D → D → Set
m ◁ n = ◁-fn m < ◁-fn n
