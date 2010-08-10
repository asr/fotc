------------------------------------------------------------------------------
-- Agda internal syntax
------------------------------------------------------------------------------

module InternalSyntax where

-- Based on Agda.Syntax.Internal

postulate
  A B C : Set

------------------------------------------------------------------------------
-- Examples

-- The term is Def
postulate defTerm : A
-- El (Type (Lit (LitLevel  0))) (Def InternalSyntax.A [])

-- The term is Fun
postulate funTerm₁ : A → B
-- {-# ATP prove funTerm₁ #-}

-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.B [])))

postulate funTerm₂ : A → B → C
-- {-# ATP prove funTerm₂ #-}

-- El (Type (Lit (LitLevel  0)))
--    (Fun (El (Type (Lit (LitLevel  0)))
--             (Def InternalSyntax.A []))
--         (El (Type (Lit (LitLevel  0)))
--             (Fun (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.B []))
--                  (El (Type (Lit (LitLevel  0)))
--                      (Def InternalSyntax.C [])))))


-- The term is a (fake) Pi
postulate piTerm : (a : A) → B
-- {-# ATP prove piTerm #-}

-- El (Type (Lit (LitLevel  0)))
--    (Pi (El (Type (Lit (LitLevel  0)))
--            (Def InternalSyntax.A []))
--        (Abs "a" El (Type (Lit (LitLevel  0)))
--                    (Def InternalSyntax.B [])))
