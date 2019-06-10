{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module BottomBottom where

open import Common.FOL.FOL

postulate bot bot' : ⊥
{-# ATP prove bot bot' #-}
{-# ATP prove bot' bot #-}

-- $ apia-fot BottomBottom.agda
-- Proving the conjecture in /tmp/BottomBottom/8-bot.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
-- Proving the conjecture in /tmp/BottomBottom/8-bot39.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
