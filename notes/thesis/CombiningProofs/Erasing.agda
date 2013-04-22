{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module CombiningProofs.Erasing where

postulate
  D     : Set
  succ₁ : D → D

data N : D → Set where
  nsucc₁ : ∀ {n} → N n → N (succ₁ n)
  nsucc₂ : ∀ {n} → (Nn : N n) → N (succ₁ n)

-- The types of nsucc₁ and nsucc₂ are the same.

-- (18 April 2013)
-- $ dump-agdai Erasing

-- Qname: Erasing.N.nsucc₁
-- Type: El {getSort = Type (Max []), unEl = Pi []r{El {getSort = Type (Max []), unEl = Def Erasing.D []}} (Abs "n" El {getSort = Type (Max []), unEl = Pi []r(El {getSort = Type (Max []), unEl = Def Erasing.N [[]r(Var 0 [])]}) (NoAbs "_" El {getSort = Type (Max []), unEl = Def Erasing.N [[]r(Def Erasing.succ₁ [[]r(Var 0 [])])]})})}

-- Qname: Erasing.N.nsucc₂
-- Type: El {getSort = Type (Max []), unEl = Pi []r{El {getSort = Type (Max []), unEl = Def Erasing.D []}} (Abs "n" El {getSort = Type (Max []), unEl = Pi []r(El {getSort = Type (Max []), unEl = Def Erasing.N [[]r(Var 0 [])]}) (NoAbs "Nn" El {getSort = Type (Max []), unEl = Def Erasing.N [[]r(Def Erasing.succ₁ [[]r(Var 0 [])])]})})}
