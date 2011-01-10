------------------------------------------------------------------------------
-- Eta expansion of Agda internal types
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.EtaExpansion ( EtaExpandible(etaExpand) ) where

-- Haskell imports

import Control.Monad.State  ( evalState, get, modify )

-- Agda library imports

-- import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common
    ( Arg(Arg)
    , Hiding(NotHidden)
    , Nat
    , Relevance(Relevant)
    )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , Args
    , arity
    , Term(Con, Def, DontCare, Fun, Lam, Lit, MetaV, Pi, Sort, Var)
    , Sort(Type)
    , Type(El)
    )
import Agda.Syntax.Literal   ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports

import AgdaLib.Interface       ( qNameType )
import AgdaLib.Syntax.DeBruijn ( increaseByOneVar )
import Monad.Base              ( T, TState(tVars) )
import Utils.Names             ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------

class EtaExpandible a where
    etaExpand ∷ a → T a

instance EtaExpandible Type where
    etaExpand (El (Type (Lit (LitLevel r n))) term)
        | n `elem` [ 0, 1 ] =
            do termEtaExpanded ← etaExpand term
               return $ El (Type (Lit (LitLevel r n))) termEtaExpanded
        | otherwise = __IMPOSSIBLE__

    etaExpand _ = __IMPOSSIBLE__

instance EtaExpandible Term where
    etaExpand (Def qName args) = do

      state ← get

      let vars ∷ [String]
          vars = tVars state

      def ← qNameType qName

      let qNameArity ∷ Nat
          qNameArity = arity def

      argsEtaExpanded ← mapM etaExpand args

      let newVar ∷ Arg Term
          newVar = Arg NotHidden Relevant (Var 0 [])

      let freshVar ∷ String
          freshVar = evalState freshName vars

      -- The eta-contraction *only* reduces by 1 the number of arguments
      -- of a term, for example:

      -- Given P : D → Set,
      -- λ x → P x eta-contracts to P or

      -- Given _≡_ : D → D → Set,
      -- (x : D) → (λ y → x ≡ y) eta-contracts to (x : D) → _≡_ x

      -- therefore we only applied the eta-expansion in this case.

      if qNameArity == fromIntegral (length args)
        then return $ Def qName argsEtaExpanded
        else if qNameArity - 1 == fromIntegral (length args)
               then do
                 modify $ \s → s { tVars = freshVar : vars }
                 -- Because we are going to add a new abstraction, we
                 -- need increase by one the numbers associated with the
                 -- variables in the arguments.
                 let incVarsEtaExpanded ∷ Args
                     incVarsEtaExpanded = map increaseByOneVar argsEtaExpanded
                 return $
                   Lam NotHidden (Abs freshVar
                                      (Def qName
                                           (incVarsEtaExpanded ++ [newVar])))
               else __IMPOSSIBLE__

    -- We don't know an example of eta-contraction with Con, therefore we
    -- don't do anything.
    etaExpand term@(Con _ _) = return term

    etaExpand (Fun tyArg ty) = do
      tyArgEtaExpanded ← etaExpand tyArg
      tyEtaExpanded    ← etaExpand ty
      return $ Fun tyArgEtaExpanded tyEtaExpanded

    etaExpand (Lam h (Abs x termAbs)) = do
      -- We add the variable x to the enviroment.
      state ← get
      let vars ∷ [String]
          vars = tVars state
      modify $ \s → s { tVars = x : vars }

      termAbsEtaExpanded ← etaExpand termAbs
      return $ Lam h (Abs x termAbsEtaExpanded)

    -- It seems it is not necessary to eta-expand the tyArg like in the
    -- case of Fun (Arg Type) Type.
    etaExpand (Pi tyArg (Abs x tyAbs)) = do
      -- We add the variable x to the enviroment.
      state ← get
      let vars ∷ [String]
          vars = tVars state
      modify $ \s → s { tVars = x : vars }

      tyAbsEtaExpanded ← etaExpand tyAbs
      return $ Pi tyArg (Abs x tyAbsEtaExpanded)

    etaExpand (Var n args) = do
      argsEtaExpanded ← mapM etaExpand args
      return $ Var n argsEtaExpanded

    etaExpand DontCare    = __IMPOSSIBLE__
    etaExpand (Lit _)     = __IMPOSSIBLE__
    etaExpand (MetaV _ _) = __IMPOSSIBLE__
    etaExpand (Sort _)    = __IMPOSSIBLE__

instance EtaExpandible a ⇒ EtaExpandible (Arg a) where
    etaExpand (Arg h r t) = do
      tEtaExpanded ← etaExpand t
      return (Arg h r tEtaExpanded)
