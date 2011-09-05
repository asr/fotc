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
  ( ChangeIndex(changeIndex)
  , IndexPlus1(indexPlus1)
  , IndexMinus1(indexMinus1)
  , removeProofTerm
  , typesOfVars
  , varToIndex
  ) where

-- Haskell imports
import Control.Monad       ( liftM2 )
import Control.Monad.Error ( throwError )

-- import Data.Maybe ( fromJust )
import Data.List  ( elemIndex )

------------------------------------------------------------------------------
-- Agda libray imports

import Agda.Syntax.Common ( Arg(Arg) , Nat )
import Agda.Syntax.Internal
  ( Abs(Abs)
  , Args
  , ClauseBody(Bind,Body)
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Tele(EmptyTel, ExtendTel)
  , Term(Con, Def, DontCare, Fun, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Sort(Type)
  , Type(El)
  )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base    ( getTVars, popTVar, pushTVar, T )
import Monad.Reports ( reportSLn )
import Utils.Show    ( showLn )

#include "../../undefined.h"

------------------------------------------------------------------------------
-- | To increase by one the de Bruijn index of the variable.
class IndexPlus1 a where
  indexPlus1 ∷ a → a

instance IndexPlus1 Term where
  indexPlus1 (Var n [])  = Var (n + 1) []
  indexPlus1 (Var _ _)   = __IMPOSSIBLE__

  indexPlus1 (Con _ _)   = __IMPOSSIBLE__
  indexPlus1 (Def _ _)   = __IMPOSSIBLE__
  indexPlus1 DontCare    = __IMPOSSIBLE__
  indexPlus1 (Fun _ _)   = __IMPOSSIBLE__
  indexPlus1 (Lam _ _)   = __IMPOSSIBLE__
  indexPlus1 (Level _)   = __IMPOSSIBLE__
  indexPlus1 (Lit _)     = __IMPOSSIBLE__
  indexPlus1 (MetaV _ _) = __IMPOSSIBLE__
  indexPlus1 (Pi _ _)    = __IMPOSSIBLE__
  indexPlus1 (Sort _)    = __IMPOSSIBLE__

-- Requires FlexibleInstances.
instance IndexPlus1 (Arg Term) where
  indexPlus1 (Arg h r term) = Arg h r $ indexPlus1 term

------------------------------------------------------------------------------
-- | To reduce by one the de Bruijn index of the variable.
class IndexMinus1 a where
  indexMinus1 ∷ a → a

instance IndexMinus1 Term where
  indexMinus1 (Def qname args) = Def qname $ indexMinus1 args

  indexMinus1 (Var 0 [])  = __IMPOSSIBLE__
  indexMinus1 (Var n [])  = Var (n - 1) []
  indexMinus1 (Var _ _)   = __IMPOSSIBLE__

  indexMinus1 (Con _ _)   = __IMPOSSIBLE__
  indexMinus1 DontCare    = __IMPOSSIBLE__
  indexMinus1 (Fun _ _)   = __IMPOSSIBLE__
  indexMinus1 (Lam _ _)   = __IMPOSSIBLE__
  indexMinus1 (Level _)   = __IMPOSSIBLE__
  indexMinus1 (Lit _)     = __IMPOSSIBLE__
  indexMinus1 (MetaV _ _) = __IMPOSSIBLE__
  indexMinus1 (Pi _ _)    = __IMPOSSIBLE__
  indexMinus1 (Sort _)    = __IMPOSSIBLE__

instance IndexMinus1 a ⇒ IndexMinus1 [a] where
  indexMinus1 = map indexMinus1

instance IndexMinus1 Type where
  indexMinus1 (El (Type (Max [])) term) = El (Type (Max [])) (indexMinus1 term)
  indexMinus1 _                         = __IMPOSSIBLE__

instance IndexMinus1 a ⇒ IndexMinus1 (Arg a) where
  indexMinus1 (Arg h r a) = Arg h r $ indexMinus1 a

instance IndexMinus1 a ⇒ IndexMinus1 (Abs a) where
  indexMinus1 (Abs name body) = Abs name $ indexMinus1 body

instance IndexMinus1 a ⇒ IndexMinus1 (Tele a) where
  indexMinus1 EmptyTel          = EmptyTel
  indexMinus1 (ExtendTel a tel) = ExtendTel (indexMinus1 a) (indexMinus1 tel)

------------------------------------------------------------------------------
-- We collect the variables' names using the type class VarNames. The
-- de Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.

class VarNames a where
  varNames ∷ a → [String]

instance VarNames Term where
  varNames (Def _ args) = varNames args

  varNames (Lam _ (Abs x term)) = varNames term ++ [x]

  varNames (Var _ [])   = []
  varNames (Var _ args) = varNames args

  varNames (Con _ _)   = __IMPOSSIBLE__
  varNames DontCare    = __IMPOSSIBLE__
  varNames (Fun _ _)   = __IMPOSSIBLE__
  varNames (Level _)   = __IMPOSSIBLE__
  varNames (Lit _)     = __IMPOSSIBLE__
  varNames (MetaV _ _) = __IMPOSSIBLE__
  varNames (Pi _ _)    = __IMPOSSIBLE__
  varNames (Sort _)    = __IMPOSSIBLE__

instance VarNames (Arg Term) where
  varNames (Arg _ _ term) = varNames term

instance VarNames Args where
  varNames []           = []
  varNames (arg : args) = varNames arg ++ varNames args

instance VarNames ClauseBody where
  varNames (Bind (Abs x cBody)) = varNames cBody ++ [x]
  varNames (Body term)          = varNames term
  varNames _                    = __IMPOSSIBLE__

-- Return the de Bruijn index of a variable in a ClauseBody.
varToIndex ∷ ClauseBody → String → Nat
varToIndex cBody x =
  case elemIndex x (varNames cBody) of
    Just n  → fromIntegral n
    Nothing → __IMPOSSIBLE__

------------------------------------------------------------------------------
-- To change a de Bruijn index with respect to other index.
-- Let's suppose we have something like

-- λ m : D → (λ n : D → (λ Nn : N n → (λ h : D → ... Var 2 ...)))

-- where 'Var 2' is the de Bruijn index of the variable n. If we
-- remove the quantification on the proof term Nn

-- λ m : D → (λ n : D → (λ h : D → ...))

-- we need change 'Var 2' by 'Var 1'.

class ChangeIndex a where
  changeIndex ∷ a → Nat → a

instance ChangeIndex Term where
  changeIndex term@(Def _ []) _ = term

  changeIndex (Def qName args) index = Def qName $ changeIndex args index

  changeIndex (Lam h (Abs x term)) index = Lam h (Abs x (changeIndex term index))

  -- When the variable is part of an argument, it was processed in the
  -- Args instance.
  changeIndex term@(Var n []) index
    -- The variable was before than the quantified variable, we don't
    -- do nothing.
    | n < index = term

    -- The variable was after than the quantified variable, we need
    -- "unbound" the quantified variable.
    | n > index = Var (n - 1) []

    | n == index = __IMPOSSIBLE__

  changeIndex (Con _ _)   _  = __IMPOSSIBLE__
  changeIndex DontCare    _  = __IMPOSSIBLE__
  changeIndex (Fun _ _)   _  = __IMPOSSIBLE__
  changeIndex (Level _)   _  = __IMPOSSIBLE__
  changeIndex (Lit _)     _  = __IMPOSSIBLE__
  changeIndex (MetaV _ _) _  = __IMPOSSIBLE__
  changeIndex (Pi _ _)    _  = __IMPOSSIBLE__
  changeIndex (Sort _)    _  = __IMPOSSIBLE__
  changeIndex (Var _ _)   _  = __IMPOSSIBLE__

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a simple
-- map, because in some cases we need to erase the term.

instance ChangeIndex Args where
  changeIndex [] _ = []

  changeIndex (Arg h r var@(Var n []) : args) index
    -- The variable was before than the quantified variable, we don't
    -- do nothing.
    | n < index = Arg h r var : changeIndex args index

    -- The variable was after than the quantified variable, we need
    -- "unbound" the quantified variable.
    | n > index = Arg h r (Var (n - 1) []) : changeIndex args index

    -- The variable is the quantified variable. This can happen when
    -- the quantified variable is used indirectly by other term via
    -- for example a where clause (see for example xxx). In this case,
    -- we remove the variable. Before this modification, we returned
    -- __IMPOSSIBLE__.
    | n == index = changeIndex args index

  changeIndex (Arg _ _ (Var _ _) : _) _ = __IMPOSSIBLE__

  changeIndex (Arg h r term : args) index = Arg h r (changeIndex term index) :
                                            changeIndex args index

instance ChangeIndex ClauseBody where
  changeIndex (Bind (Abs x cBody)) index = Bind (Abs x (changeIndex cBody index))
  changeIndex (Body term)          index = Body $ changeIndex term index
  changeIndex _                    _     = __IMPOSSIBLE__

------------------------------------------------------------------------------
-- Remove references to variables which are proof terms from
-- the Agda internal types.

------------------------------------------------------------------------------
-- General description
-- Example (Test.Succeed.Conjectures.DefinitionsInsideWhereClauses)

-- +-rightIdentity : ∀ {n} → N n → n + zero ≡ n
-- +-rightIdentity Nn = indN P P0 iStep Nn
--   where
--     P : D → Set
--     P i = i + zero ≡ i
--     {-# ATP definition P #-}

--     postulate
--       P0 : P zero
--     {-# ATP prove P0 #-}

--     postulate
--       iStep : ∀ {i} → N i → P i → P (succ i)
--     {-# ATP prove iStep #-}

-- The Agda internal type of P0 is

-- El (Type (Max []))
--    (Pi r{El (Type (Max [])) (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.D [])}
--        (Abs ".n" El (Type (Max []))
--                     (Pi r(El (Type (Max [])) (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.N [r(Var 0 [])]))
--                         (Abs "Nn" El (Type (Max []))
--                                      (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []},r(Var 0 []),r(Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.zero [])])))))

-- The variable Nn is a proof term (i.e. Nn : N n) and it is referenced in

-- Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []},r(Var 0 [])...       (1)

-- using its de Brujin name, i.e. r(Var 0 []). After remove this
-- reference the internal term (1) is converted to

-- Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []}...].

-- In addition the quantification on Nn will be removed too. See
-- FOL.Translation.Internal.Terms.termToFormula (on Pi terms).

-- End general description.
------------------------------------------------------------------------------

-- We only need to remove the variables which are proof terms, so we
-- collect the types of the variables using the type class
-- TypesOfVars. The de Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.

class TypesOfVars a where
  typesOfVars ∷ a → [(String, Type)]

instance TypesOfVars Type where
  typesOfVars (El (Type _) term) = typesOfVars term
  typesOfVars _                  = __IMPOSSIBLE__

instance TypesOfVars Term where
  -- TDOO: In Lam terms we bound variables, but they seem doesn't have associated
  -- types. Therefore, we associate a "DontCare" type.
  -- typesOfVars (Lam _ (Abs x absTerm)) =
  --   typesOfVars absTerm ++ [(x, El (Type (Max [])) DontCare)]

  -- We only have real bounded variables in Pi terms.
  typesOfVars (Pi (Arg _ _ ty) (Abs x absTy)) = (x, ty) : typesOfVars absTy

  typesOfVars (Def _ args) = typesOfVars args

  typesOfVars (Fun _ ty) = typesOfVars ty

  typesOfVars (Con _ _)   = []
  typesOfVars DontCare    = []
  typesOfVars (Lam _ _)   = []
  typesOfVars (Level _)   = []
  typesOfVars (Lit _)     = []
  typesOfVars (MetaV _ _) = []
  typesOfVars (Sort _)    = []
  typesOfVars (Var _ _)   = []

instance TypesOfVars (Arg Term) where
  typesOfVars (Arg _ _ term) = typesOfVars term

instance TypesOfVars Args where
  typesOfVars []       = []
  typesOfVars (x : xs) = typesOfVars x ++ typesOfVars xs

-- instance TypesOfVars (Abs Type) where
--   typesOfVars (Abs _ ty) = typesOfVars ty

-- Remove the reference to a variable (i.e. Var n args) from an Agda
-- internal entity.
class RemoveVar a where
  removeVar ∷ a → String → T a

instance RemoveVar Type where
  removeVar (El ty@(Type _) term) x = fmap (El ty) (removeVar term x)
  removeVar _                     _ = __IMPOSSIBLE__

instance RemoveVar Term where
  removeVar (Def qname args) x = fmap (Def qname) (removeVar args x)

  -- N.B. The variables *are* removed from the (Arg Type).
  removeVar (Fun argT ty) x = liftM2 Fun (removeVar argT x) (removeVar ty x)

  removeVar (Lam h (Abs y absTerm)) x = do

    pushTVar y

    reportSLn "removeVar" 20 $ "Pushed variable: " ++ y

    auxTerm ← removeVar absTerm x

    popTVar

    reportSLn "removePT" 20 $ "Pop variable: " ++ y

    return $ Lam h (Abs y auxTerm)

  -- N.B. The variables *are not* removed from the (Arg Type), they
  -- are only removed from the (Abs Type).
  removeVar (Pi argT (Abs y absTy)) x = do

    pushTVar y
    reportSLn "removeVar" 20 $ "Pushed variable: " ++ y

    -- If the Pi term is on a proof term, we replace it by a Fun term.
    newTerm ← if y /= x
                then do
                  newType ← removeVar absTy x
                  return $ Pi argT (Abs y newType)
                else fmap (Fun argT) (removeVar absTy x)
    popTVar
    reportSLn "removePT" 20 $ "Pop variable: " ++ y
    return newTerm

  removeVar (Con _ _)   _ = __IMPOSSIBLE__
  removeVar DontCare    _ = __IMPOSSIBLE__
  removeVar (Level _)   _ = __IMPOSSIBLE__
  removeVar (Lit _)     _ = __IMPOSSIBLE__
  removeVar (MetaV _ _) _ = __IMPOSSIBLE__
  removeVar (Sort _)    _ = __IMPOSSIBLE__
  removeVar (Var _ _)   _ = __IMPOSSIBLE__

instance RemoveVar (Arg Type) where
  removeVar (Arg h r ty) x = fmap (Arg h r) (removeVar ty x)

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a map,
-- because in some cases we need to erase the term.

-- Requires TypeSynonymInstances.
instance RemoveVar Args where
  removeVar [] _ = return []

  removeVar (Arg h r var@(Var n []) : args) x = do

    vars ← getTVars

    let index ∷ Integer
        index = case elemIndex x vars of
                  Nothing →  __IMPOSSIBLE__
                  Just i  → fromIntegral i

    if n == index
      then removeVar args x
      else if n < index
             then fmap ((:) (Arg h r var)) (removeVar args x)
             else fmap ((:) (Arg h r (Var (n - 1) []))) (removeVar args x)

  removeVar (Arg _ _ (Var _ _) : _) _ = __IMPOSSIBLE__

  removeVar (Arg h r term : args) x =
    liftM2 (\t ts → Arg h r t : ts) (removeVar term x) (removeVar args x)

removeProofTerm ∷ Type → (String, Type) → T Type
removeProofTerm ty (x, typeVar) = do
  reportSLn "removePT" 20 $ "Removing variable: " ++ x

  case typeVar of
    -- The variable's type is a Set,
    --
    -- e.g. the variable is d : D, where D : Set
    --
    -- so we don't do anything.

    -- N.B. the pattern matching on (Def _ []).
    El (Type (Max [])) (Def _ []) → return ty

    -- The variable's type is a proof,
    --
    -- e.g. the variable is 'Nn : N n' where D : Set, n : D and N :
    -- D → Set.
    --
    -- In this case, we remove the reference to this
    -- variable.

    -- N.B. the pattern matching on (Def _ _).

    El (Type (Max [])) (Def _ _) → removeVar ty x

    -- The variable's type is a function type,
    --
    -- e.g. the variable is f : D → D, where D : Set.

    -- -- In the class TypesOfVar we associated to the variables bounded
    -- -- in Lam terms the type DontCare.
    -- El (Type (Max [])) DontCare → return ty

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Fun (Arg _ _ (El (Type (Max [])) (Def _ [])))
            (El (Type (Max [])) (Def _ []))
       ) → return ty

    -- The next case is just a generalization to various arguments of
    -- the previous case.

    -- The variable's type is a function type,
    --
    -- e.g. the variable is f : D → D → D, where D : Set.

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Fun (Arg _ _ (El (Type (Max [])) (Def _ [])))
            (El (Type (Max [])) (Fun _ _))
       ) → return ty

    -- We don't erase these proofs terms.
    El (Type (Max [])) someTerm → do
      reportSLn "removePT" 20 $
                "The term someTerm is: " ++ show someTerm
      throwError $ "It is necessary to erase the proof term\n"
                   ++ showLn someTerm
                   ++ "but we do not know how to do it"

    -- The variable's type is Set₁,
    --
    -- e.g. the variable is P : Set.
    --
    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max [ClosedLevel 1])) (Sort _) → return ty

    -- N.B. The next case is just a generalization to various
    -- arguments of the previous case.

    -- The variable's type is Set₁,
    --
    -- e.g. the variable is P : D → Set.
    --
    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max [ClosedLevel 1])) (Fun _ _) → return ty

    -- Other cases
    El (Type (Max [ClosedLevel 1])) (Def _ _)    → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) DontCare     → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Con _ _)    → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Lam _ _)    → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (MetaV _ _)  → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Pi _ _)     → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Var _ _)    → __IMPOSSIBLE__

    someType → do
      reportSLn "removePT" 20 $
                "The type varType is: " ++ show someType
      __IMPOSSIBLE__
