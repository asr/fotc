------------------------------------------------------------------------------
-- Agda internal syntax
------------------------------------------------------------------------------

module InternalSyntax where

-- Based on Agda.Syntax.Internal

postulate A : Set

------------------------------------------------------------------------------
-- Examples

-- The term is Def
postulate termDef : A
-- El (Type (Lit (LitLevel  0))) (Def InternalSyntax.A [])

-- The term is Fun
postulate termFun1 : A → A
-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A [])))

postulate termFun2 : A → A → A
-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Fun (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.A []))
--                  (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.A [])))))

-- The term is a (fake) Pi
postulate termPi : (a : A) → A
-- El (Type (Lit (LitLevel  0)))
--    (Pi (El (Type (Lit (LitLevel  0)))
--            (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Lit (LitLevel  0)))
--                    (Def InternalSyntax.A [])))
