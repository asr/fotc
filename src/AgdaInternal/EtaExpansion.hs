------------------------------------------------------------------------------
-- |
-- Module      : AgdaLib.EtaExpansion
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Eta expansion of Agda internal types.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaInternal.EtaExpansion ( EtaExpandible(etaExpand) ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( when )
import Control.Monad.Error ( MonadError(throwError) )

import Data.Functor ( (<$>) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg)
  , Dom(Dom)
  , Hiding(NotHidden)
  , Nat
  , Relevance(Relevant)
  )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Args
  , arity
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Term(Con, Def, Lam, Pi, Var)
  , Sort(Type)
  , Type(El)
  , var
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( whenM )

------------------------------------------------------------------------------
-- Local imports

import AgdaInternal.DeBruijn  ( IncIndex(incIndex) )
import AgdaInternal.Interface ( isProjection, qNameType )
import Monad.Base             ( newTVar, T )

#include "../undefined.h"

------------------------------------------------------------------------------

-- N.B. The class doesn't use the state of the translation monad,
-- therefore it is not necessary to test for a clean state after its
-- use.

-- | Eta-expandible entities.
class EtaExpandible a where
  etaExpand ∷ a → T a

instance EtaExpandible Type where
  etaExpand (El (Type (Max [])) term) =  El (Type (Max [])) <$> etaExpand term

  etaExpand (El (Type (Max [ClosedLevel 1])) term) =
    El (Type (Max [ClosedLevel 1])) <$> etaExpand term

  etaExpand _ = __IMPOSSIBLE__

instance EtaExpandible Term where
  etaExpand (Def qName args) = do
    whenM (isProjection qName) $
          throwError $
            "The translation of projection-like functions as "
            ++ show qName
            ++ " is not implemented"

    qNameArity ∷ Nat ← arity <$> qNameType qName

    argsEtaExpanded ← mapM etaExpand args

    -- The eta-contraction *only* reduces by 1 the number of arguments
    -- of a term, for example:

    -- Given @P : D → Set@,
    -- @λ x → P x@ eta-contracts to @P@ or

    -- Given @_≡_ : D → D → Set@,
    -- @(x : D) → (λ y → x ≡ y)@ eta-contracts to @(x : D) → _≡_ x@

    -- therefore we only applied the eta-expansion in this case.

    if qNameArity == fromIntegral (length args)
      then return $ Def qName argsEtaExpanded
      else do
        when (qNameArity - 1 /= fromIntegral (length args)) (__IMPOSSIBLE__)

        -- Because we are going to add a new abstraction, we need
        -- increase by one the numbers associated with the variables
        -- in the arguments.
        let incVarsEtaExpanded ∷ Args
            incVarsEtaExpanded = map incIndex argsEtaExpanded

            newVar ∷ Arg Term
            newVar = Arg NotHidden Relevant (var 0)

        freshVar ← newTVar

        return $ Lam NotHidden
                     (Abs freshVar (Def qName (incVarsEtaExpanded ++ [newVar])))

  -- We don't know an example of eta-contraction with @Con@, therefore
  -- we don't do anything.
  etaExpand term@(Con _ _) = return term

  etaExpand (Lam h (Abs x termAbs)) = Lam h . Abs x <$> etaExpand termAbs

  etaExpand (Pi tyArg (NoAbs x tyAbs)) = do
     tArg ← etaExpand tyArg
     tAbs ← etaExpand tyAbs
     return $ Pi tArg (NoAbs x tAbs)
  -- It seems it is not necessary to eta-expand the @tyArg@ like in the
  -- case of @Pi _ (NoAbs _ _)@.
  etaExpand (Pi tyArg (Abs x tyAbs)) = Pi tyArg . Abs x <$> etaExpand tyAbs

  etaExpand (Var n args) = Var n <$> mapM etaExpand args

  etaExpand _ = __IMPOSSIBLE__

instance EtaExpandible a ⇒ EtaExpandible (Arg a) where
  etaExpand (Arg h r e) = Arg h r <$> etaExpand e

instance EtaExpandible a ⇒ EtaExpandible (Dom a) where
  etaExpand (Dom h r e) = Dom h r <$> etaExpand e
