------------------------------------------------------------------------------
-- Functions on Agda internal syntax entities
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances, UnicodeSyntax #-}

module MyAgda.Syntax.Internal ( increaseByOneVar, renameVar ) where

-- Agda libray imports
import Agda.Syntax.Common
    ( Arg(Arg)
    , Nat
    )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , ClauseBody(Bind,Body)
    , Term(Def, Con, Fun, Lam, Lit, MetaV, Pi, Sort, Var)
    )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
#include "../../undefined.h"

------------------------------------------------------------------------------
-- There are various cases (e.g. eta-expansion, translation of
-- symbols' definitions, elimination of quantification on variables
-- which are proof terms) where it is necessary modify the variables
-- in the Agda internal terms, i.e. it is necessary to modify the
-- Bruijn index in the variable.

-- To increase by one the Bruijn index of the variable.
class IncreaseByOneVar a where
    increaseByOneVar :: a → a

instance IncreaseByOneVar Term where
    increaseByOneVar (Var n [])   = Var (n + 1) []
    increaseByOneVar (Var _ _ )   = __IMPOSSIBLE__
    increaseByOneVar (Con _ _ )   = __IMPOSSIBLE__
    increaseByOneVar (Def _ _ )   = __IMPOSSIBLE__
    increaseByOneVar (Fun _ _ )   = __IMPOSSIBLE__
    increaseByOneVar (Lam _ _ )   = __IMPOSSIBLE__
    increaseByOneVar (Lit _  )    = __IMPOSSIBLE__
    increaseByOneVar (MetaV _ _ ) = __IMPOSSIBLE__
    increaseByOneVar (Pi _ _ )    = __IMPOSSIBLE__
    increaseByOneVar (Sort _ )    = __IMPOSSIBLE__

instance IncreaseByOneVar (Arg Term) where -- Requires FlexibleInstances
    increaseByOneVar (Arg h term) = Arg h $ increaseByOneVar term

-- To rename a Bruijn index with respect to a position of a variable.
class RenameVar a where
    renameVar :: a → Nat → a

instance RenameVar Term where
    renameVar term@(Def _ [])  _   = term

    renameVar (Def qName args) pos = Def qName $ map (`renameVar` pos) args

    renameVar term@(Var n []) pos =
        if n < pos
           then term -- The variable was before than the quantified variable,
                     -- we don't do nothing.
           else if n > pos
                then Var (n - 1) [] -- The variable was after than the
                                    -- quantified variable, we need
                                    -- "unbound" the quantified variable.
                else __IMPOSSIBLE__

    renameVar (Var _ _ )   _   = __IMPOSSIBLE__
    renameVar (Con _ _ )   _   = __IMPOSSIBLE__
    renameVar (Fun _ _ )   _   = __IMPOSSIBLE__
    renameVar (Lam _ _ )   _   = __IMPOSSIBLE__
    renameVar (Lit _  )    _   = __IMPOSSIBLE__
    renameVar (MetaV _ _ ) _   = __IMPOSSIBLE__
    renameVar (Pi _ _ )    _   = __IMPOSSIBLE__
    renameVar (Sort _ )    _   = __IMPOSSIBLE__

instance RenameVar (Arg Term) where -- Requires FlexibleInstances
    renameVar (Arg h term) pos = Arg h $ renameVar term pos

instance RenameVar ClauseBody where
    renameVar (Bind (Abs var cBody)) pos = Bind (Abs var (renameVar cBody pos))
    renameVar (Body term)            pos = Body $ renameVar term pos
    renameVar _                      _   = __IMPOSSIBLE__
