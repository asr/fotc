------------------------------------------------------------------------------
-- Agda internal syntax
------------------------------------------------------------------------------

module InternalSyntax where

-- Based on Agda.Syntax.Internal

postulate
  A B C : Set
-- Internal type (old representation):
-- El (Type (Lit (LitLevel  1))) (Sort (Type (Lit (LitLevel  0))))

-- Internal type (new representation 2011-06-19):
-- El (Type (Max [ClosedLevel 1])) (Sort (Type (Max [])))

------------------------------------------------------------------------------
-- Examples

-- The term is Def
postulate defTerm : A
-- Internal type (old representation):
-- El (Type (Max [])) (Def InternalSyntax.A [])

-- Internal type (new representation 2011-06-19):
-- El (Type (Lit (LitLevel  0))) (Def InternalSyntax.A [])

-- The term is Fun
postulate funTerm₁ : A → B
-- Internal type (old representation):
-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.B [])))

-- Internal type (new representation 2011-06-19):
-- El (Type (Max []))
--     (Fun r(El (Type (Max []))
--               (Def InternalSyntax.A []))
--          (El (Type (Max []))
--              (Def InternalSyntax.B [])))


postulate funTerm₂ : A → B → C
-- Internal type (old representation):
-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Fun (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.B []))
--                  (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.C [])))))

-- Internal type (new representation 2011-06-19):
-- El (Type (Max []))
--    (Fun r(El (Type (Max []))
--              (Def InternalSyntax.A []))
--         (El (Type (Max []))
--             (Fun r(El (Type (Max []))
--                       (Def InternalSyntax.B []))
--                  (El (Type (Max []))
--                      (Def InternalSyntax.C [])))))


-- The term is a (fake) Pi
postulate piTerm : (a : A) → B
-- Internal type (old representation):
-- El (Type (Lit (LitLevel  0)))
--    (Pi (El (Type (Lit (LitLevel  0)))
--            (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Lit (LitLevel  0)))
--                    (Def InternalSyntax.B [])))

-- Internal type (new representation 2011-06-19):
-- El (Type (Max []))
--    (Pi r(El (Type (Max []))
--             (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Max []))
--                 (Def InternalSyntax.B [])))
