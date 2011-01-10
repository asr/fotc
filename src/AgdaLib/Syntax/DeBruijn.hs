------------------------------------------------------------------------------
-- Functions on de Bruijn indexes
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

-- There are various cases (e.g. eta-expansion, translation of
-- symbols' definitions, elimination of quantification on variables
-- which are proof terms) where it is necessary modify the variables
-- in the Agda internal terms, i.e. it is necessary to modify the
-- Bruijn index in the variable.

module AgdaLib.Syntax.DeBruijn
    ( IncreaseByOneVar(increaseByOneVar)
    , RenameVar(renameVar)
    , removeReferenceToProofTerms
    , varToDeBruijnIndex
    ) where

-- Haskell imports
import Data.List ( elemIndex )

-- Agda libray imports
import Agda.Syntax.Common
    ( Arg(Arg)
    , Nat
    )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , Args
    , ClauseBody(Bind,Body)
    , Term(Con, Def, DontCare, Fun, Lam, Lit, MetaV, Pi, Sort, Var)
    , Sort(Type)
    , Type(El)
    )
import Agda.Syntax.Literal   ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
#include "../../undefined.h"

------------------------------------------------------------------------------
-- | To increase by one the de Bruijn index of the variable.
class IncreaseByOneVar a where
    increaseByOneVar ∷ a → a

instance IncreaseByOneVar Term where
    increaseByOneVar (Var n [])  = Var (n + 1) []
    increaseByOneVar (Var _ _)   = __IMPOSSIBLE__
    increaseByOneVar (Con _ _)   = __IMPOSSIBLE__
    increaseByOneVar (Def _ _)   = __IMPOSSIBLE__
    increaseByOneVar DontCare    = __IMPOSSIBLE__
    increaseByOneVar (Fun _ _)   = __IMPOSSIBLE__
    increaseByOneVar (Lam _ _)   = __IMPOSSIBLE__
    increaseByOneVar (Lit _)     = __IMPOSSIBLE__
    increaseByOneVar (MetaV _ _) = __IMPOSSIBLE__
    increaseByOneVar (Pi _ _)    = __IMPOSSIBLE__
    increaseByOneVar (Sort _)    = __IMPOSSIBLE__

-- Requires FlexibleInstances.
instance IncreaseByOneVar (Arg Term) where
    increaseByOneVar (Arg h r term) = Arg h r $ increaseByOneVar term

------------------------------------------------------------------------------
-- We collect the variables' names using the type class VarNames. The
-- de Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.

class VarNames a where
    varNames ∷ a → [String]

instance VarNames ClauseBody where
    varNames (Bind (Abs x cBody)) = varNames cBody ++ [x]
    varNames (Body _)            = []
    varNames _                   = __IMPOSSIBLE__

-- Return the de Bruijn index of a variable in a ClauseBody.
varToDeBruijnIndex ∷ ClauseBody → String → Nat
varToDeBruijnIndex cBody x =
    case elemIndex x (varNames cBody) of
      Just n  → fromIntegral n
      Nothing → __IMPOSSIBLE__

------------------------------------------------------------------------------
-- To rename a de Bruijn index with respect to other index.
-- Let's suppose we have something like

-- λ m : D → (λ n : D → (λ Nn : N n → (λ h : D → ... Var 2 ...)))

-- where 'Var 2' is the de Bruijn index of the variable n. If we
-- remove the quantification on the proof term Nn

-- λ m : D → (λ n : D → (λ h : D → ... ))

-- we need rename 'Var 2' by 'Var 1'.

class RenameVar a where
    renameVar ∷ a → Nat → a

instance RenameVar Term where
    renameVar term@(Def _ [])  _     = term

    renameVar (Def qName args) index = Def qName $ renameVar args index

    renameVar term@(Var n [])  index
      | n < index = term            -- The variable was before than
                                    -- the quantified variable, we
                                    -- don't do nothing.

      | n > index = Var (n - 1) []  -- The variable was after than the
                                    -- quantified variable, we need
                                    -- "unbound" the quantified
                                    -- variable.

      | otherwise = __IMPOSSIBLE__

    renameVar (Var _ _)   _   = __IMPOSSIBLE__
    renameVar (Con _ _)   _   = __IMPOSSIBLE__
    renameVar DontCare    _   = __IMPOSSIBLE__
    renameVar (Fun _ _)   _   = __IMPOSSIBLE__
    renameVar (Lam _ _)   _   = __IMPOSSIBLE__
    renameVar (Lit _)     _   = __IMPOSSIBLE__
    renameVar (MetaV _ _) _   = __IMPOSSIBLE__
    renameVar (Pi _ _)    _   = __IMPOSSIBLE__
    renameVar (Sort _)    _   = __IMPOSSIBLE__

-- Requires FlexibleInstances.
instance RenameVar (Arg Term) where
    renameVar (Arg h r term) index = Arg h r $ renameVar term index

instance RenameVar Args where
    renameVar []           _   = []
    renameVar (arg : args) index = renameVar arg index : renameVar args index

instance RenameVar ClauseBody where
    renameVar (Bind (Abs x cBody)) index = Bind (Abs x (renameVar cBody index))
    renameVar (Body term)          index = Body $ renameVar term index
    renameVar _                    _     = __IMPOSSIBLE__

------------------------------------------------------------------------------
-- Remove references to variables which are proof terms from
-- the Agda internal types.

-- General description
-- Example
-- +-leftIdentity : {n : D} → N n → zero + n ≡ n
-- +-leftIdentity {n} Nn = indN P P0 iStep Nn
--   where
--     P : D → Set
--     P i = zero + i ≡ i
--     {-# ATP definition P #-}

--     postulate
--       P0 : P zero
--     {-# ATP prove P0 #-}

--     postulate
--       iStep : {i : D} → N i → P i → P (succ i)
--     {-# ATP prove iStep #-}

-- The Agda internal type of P0 is

-- El (Type (Lit (LitLevel  0)))
--    (Pi {El (Type (Lit (LitLevel  0))) (Def Test.Test.D [])}
--        (Abs "n" El (Type (Lit (LitLevel  0)))
--                    (Pi (El (Type (Lit (LitLevel  0))) (Def Test.Test.N [(Var 0 [])]))
--                        (Abs "Nn" El (Type (Lit (LitLevel  0)))
--                                     (Def Test.Test._.P [{Var 1 []},(Var 0 []),(Def Test.Test.zero [])])))))

-- The variable Nn is a proof term (i.e. Nn : N n) and it is referenced in

-- Def Test.Test._.P [{Var 1 []},(Var 0 []), ...]       (1)

-- using its de Brujin name (i.e. (Var 0 [])). After remove this
-- reference (1) is converted to

-- Def Test.Test._.P [{Var 1 []}, ...].

-- In addition the quantification on Nn will be removed too. See
-- FOL.Translation.Internal.Terms.termToFormula (on Pi terms).

-- End general description.

-- We only need to remove the variables which are proof terms, so we
-- collect the variables' types using the type class VarsTypes. The de
-- Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.
class VarsTypes a where
    varsTypes ∷ a → [ Type ]

instance VarsTypes Type where
    varsTypes (El (Type _) term) = varsTypes term
    varsTypes _                  = __IMPOSSIBLE__

instance VarsTypes Term where
    varsTypes (Pi (Arg _ _ ty) absT) = varsTypes absT ++ [ ty ]
    -- We only have bounded variables in Pi terms.
    varsTypes _                      = []

instance VarsTypes (Abs Type) where
    varsTypes (Abs _ ty) = varsTypes ty

-- Remove the reference to a variable (i.e. Var n args) from an Agda
-- internal entity.
class RemoveVar a where
    removeVar ∷ a → Nat → a  -- The Nat represents the de Bruijn index
                              -- of the variable to be removed.

instance RemoveVar Type where
    removeVar (El ty@(Type _) term) index  = El ty (removeVar term index)
    removeVar _                     _      = __IMPOSSIBLE__

instance RemoveVar Term where
    -- We only need remove variables from Def terms.
    removeVar (Def qname args) index = Def qname $ removeVar args index
    removeVar (Fun argT ty) index =
        Fun (removeVar argT index) $ removeVar ty index
    -- N.B. The variables *are not* removed from the (Arg Type), they are
    -- only removed from the (Abs Type).
    removeVar (Pi argT absT) index = Pi argT $ removeVar absT index
    removeVar _              _     = __IMPOSSIBLE__

instance RemoveVar (Abs Type) where
    removeVar (Abs h ty) index = Abs h $ removeVar ty index

instance RemoveVar (Arg Type) where
    removeVar (Arg h r ty) index = Arg h r $ removeVar ty index

-- Requires TypeSynonymInstances.
-- This instance does the job. This remove the variable.
instance RemoveVar Args where
    removeVar [] _ = []
    removeVar (Arg h r var@(Var n _) : args) index =
        if n == index
           then removeVar args index
           else Arg h r var : removeVar args index
    removeVar (Arg h r t : args) index = Arg h r t : removeVar args index

removeReferenceToProofTerm ∷ Type → Nat → Type → Type
removeReferenceToProofTerm varType index ty =
    case varType of
      -- The variable's type is a Set,
      --
      -- e.g. the variable is d : D, where D : Set
      --
      -- so we don't do anything.  N.B. the pattern matching on (Def _
      -- []).
      El (Type (Lit (LitLevel _ 0))) (Def _ []) → ty

      -- The variable's type is a proof,
      --
      -- e.g. the variable is 'Nn : N n' where D : Set, n : D and N :
      -- D → Set.
      --
      -- In this case, we remove the reference to this
      -- variable. N.B. the pattern matching on (Def _ _).
      El (Type (Lit (LitLevel _ 0))) (Def _ _) → removeVar ty index

      -- The variable type is a function type,
      --
      -- e.g. the variable is f : D → D, where D : Set.  Due to the
      -- hack in FOL.Translation.Internal.Terms.termToFormula we don't
      -- do anything.
      El (Type (Lit (LitLevel _ 0)))
         (Fun (Arg _ _ (El (Type (Lit (LitLevel _ 0))) (Def _ [])))
              (El (Type (Lit (LitLevel _ 0))) (Def _ []))
         ) → ty

      -- The variable type is Set₁,
      --
      -- e.g. the variable is 'A : Set',
      --
      -- we don't know any reference to some variable in this case,
      -- therefore we don't do anything.
      El (Type (Lit (LitLevel _ 1))) (Sort _) → ty
      El (Type (Lit (LitLevel _ 1))) _        → __IMPOSSIBLE__
      _                                       → __IMPOSSIBLE__

removeReferenceToProofTerms ∷ Type → Type
removeReferenceToProofTerms ty = aux (varsTypes ty) 0 ty
    where
      aux ∷ [Type] → Nat → Type → Type
      aux []             _     tya = tya
      aux (varType : xs) index tya =
          aux xs (index + 1) $ removeReferenceToProofTerm varType index tya
