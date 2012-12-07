------------------------------------------------------------------------------
-- Agda internal syntax
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module InternalSyntax where

-- Internal types from Agda.Syntax.Internal.

------------------------------------------------------------------------------
-- Sets

postulate A B C : Set

-- El (Type (Max [ClosedLevel 1])) (Sort (Type (Max [])))

postulate A₁ : Set₁

-- El (Type (Max [ClosedLevel 2])) (Sort (Type (Max [ClosedLevel 1])))

------------------------------------------------------------------------------
-- The term is Def

postulate defTerm : A

-- El (Type (Max [])) (Def InternalSyntax.A [])

------------------------------------------------------------------------------
-- The term is Fun

postulate funTerm₁ : A → B

-- El (Type (Max []))
--    (Fun r(El (Type (Max []))
--              (Def InternalSyntax.A []))
--         (El (Type (Max []))
--             (Def InternalSyntax.B [])))

postulate funTerm₂ : A → B → C

-- El (Type (Max []))
--    (Fun r(El (Type (Max []))
--              (Def InternalSyntax.A []))
--         (El (Type (Max []))
--             (Fun r(El (Type (Max []))
--                       (Def InternalSyntax.B []))
--                  (El (Type (Max []))
--                      (Def InternalSyntax.C [])))))


------------------------------------------------------------------------------
-- The term is a (fake) Pi

postulate fakePiTerm : (a : A) → B

-- El (Type (Max []))
--    (Pi r(El (Type (Max []))
--             (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Max []))
--                 (Def InternalSyntax.B [])))

------------------------------------------------------------------------------
-- The term is Pi

postulate P : A → Set

-- El (Type (Max [ClosedLevel 1]))
--    (Fun r(El (Type (Max []))
--              (Def InternalSyntax.A []))
--         (El (Type (Max [ClosedLevel 1]))
--             (Sort (Type (Max [])))))

postulate piTerm : (a : A) → P a

-- El (Type (Max []))
--    (Pi r(El (Type (Max []))
--             (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Max []))
--                    (Def InternalSyntax.P [r(Var 0 [])])))
