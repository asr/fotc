{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Tested with the development version of the Agda standard library on
-- 27 May 2011.

-- Nils' idea about databases in the Agda mailing list.
-- http://thread.gmane.org/gmane.comp.lang.agda/2911/focus=2917

module FOT.Agsy.DataBase where

open import Data.Nat
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

postulate
  right-identity : ∀ n → n + 0 ≡ n
  move-suc       : ∀ m n → suc (m + n) ≡ m + suc n

db = right-identity ,′ move-suc

comm : ∀ m n → m + n ≡ n + m  -- Via auto {!-c db!}
comm zero n     = sym (proj₁ db n)
comm (suc n) n' =
  begin
    suc (n + n') ≡⟨ cong suc (comm n n') ⟩
    suc (n' + n) ≡⟨ proj₂ db n' n ⟩ (n' + suc n)
  ∎
