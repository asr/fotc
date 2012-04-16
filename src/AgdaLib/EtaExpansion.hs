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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.EtaExpansion ( EtaExpandible(etaExpand) ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>), (>>=), fail) )
#endif
import Control.Monad ( mapM, Monad(return) )

import Control.Monad.Error ( MonadError(throwError) )

import Data.Eq       ( Eq((==)) )
import Data.Function ( ($), (.) )
import Data.Functor  ( (<$>) )
import Data.List     ( (++), length, map )
import Data.Maybe    ( Maybe(Just, Nothing) )

#if __GLASGOW_HASKELL__ == 612
import Prelude ( fromInteger )
#endif
import Prelude ( fromIntegral, Num((-)) )

import Text.Show ( Show(show) )

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
  , Term(Con, Def, DontCare, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Sort(Type)
  , Type(El)
  , var
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.DeBruijn  ( IncIndex(incIndex) )
import AgdaLib.Interface ( isProjection, qNameType )
import Monad.Base        ( newTVar, T )
import Monad.Reports     ( reportSLn )
import Utils.Show        ( showLn )

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
    p ← isProjection qName
    case p of
      Nothing → return ()
      Just _  → throwError $
             "The translation of projection-like functions as "
             ++ show qName
             ++ " is not implemented"

    qNameArity ∷ Nat ← arity <$> qNameType qName

    argsEtaExpanded ← mapM etaExpand args

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
               -- Because we are going to add a new abstraction, we
               -- need increase by one the numbers associated with the
               -- variables in the arguments.
               let incVarsEtaExpanded ∷ Args
                   incVarsEtaExpanded = map incIndex argsEtaExpanded

                   newVar ∷ Arg Term
                   newVar = Arg NotHidden Relevant (var 0)

               freshVar ← newTVar

               return $
                 Lam NotHidden
                     (Abs freshVar (Def qName (incVarsEtaExpanded ++ [newVar])))
             else do
               reportSLn "etaExpand" 20 $
                 "qname: " ++ showLn qName
                 ++ "qNameArity: " ++ showLn qNameArity
                 ++ "length args: " ++ show (length args)
               __IMPOSSIBLE__

  -- We don't know an example of eta-contraction with Con, therefore
  -- we don't do anything.
  etaExpand term@(Con _ _) = return term

  etaExpand (Lam h (Abs x termAbs)) = Lam h . Abs x <$> etaExpand termAbs

  etaExpand (Pi tyArg (NoAbs x tyAbs)) = do
     tArg ← etaExpand tyArg
     tAbs ← etaExpand tyAbs
     return $ Pi tArg (NoAbs x tAbs)
  -- It seems it is not necessary to eta-expand the tyArg like in the
  -- case of Pi _ (NoAbs _ _).
  etaExpand (Pi tyArg (Abs x tyAbs)) = Pi tyArg . Abs x <$> etaExpand tyAbs

  etaExpand (Var n args) = Var n <$> mapM etaExpand args

  etaExpand (DontCare _)        = __IMPOSSIBLE__
  etaExpand (Level _)           = __IMPOSSIBLE__
  etaExpand (Lam _ (NoAbs _ _)) = __IMPOSSIBLE__
  etaExpand (Lit _)             = __IMPOSSIBLE__
  etaExpand (MetaV _ _)         = __IMPOSSIBLE__
  etaExpand (Sort _)            = __IMPOSSIBLE__

instance EtaExpandible a ⇒ EtaExpandible (Arg a) where
  etaExpand (Arg h r t) = Arg h r <$> etaExpand t

instance EtaExpandible a ⇒ EtaExpandible (Dom a) where
  etaExpand (Dom h r t) = Dom h r <$> etaExpand t
