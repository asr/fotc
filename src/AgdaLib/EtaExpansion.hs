------------------------------------------------------------------------------
-- Eta expansion of Agda internal types
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.EtaExpansion ( etaExpand ) where

-- Haskell imports
import Control.Monad ( liftM2 )

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
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Term(Con, Def, DontCare, Fun, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Sort(Type)
  , Type(El)
  )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports

import AgdaLib.Interface       ( qNameType )
import AgdaLib.Syntax.DeBruijn ( indexPlus1 )
import Monad.Base              ( newTVar, T )
import Monad.Reports           ( reportSLn )

#include "../undefined.h"

------------------------------------------------------------------------------

-- N.B. The class doesn't use the state of the translation monad,
-- therefore it is not necessary to test for a clean state after its
-- use.

class EtaExpandible a where
  etaExpand ∷ a → T a

instance EtaExpandible Type where
  etaExpand (El (Type (Max [])) term) =
    fmap (El (Type (Max []))) (etaExpand term)

  etaExpand (El (Type (Max [ClosedLevel 1])) term) =
    fmap (El (Type (Max [ClosedLevel 1]))) (etaExpand term)

  etaExpand _ = __IMPOSSIBLE__

instance EtaExpandible Term where
  etaExpand (Def qName args) = do

    def ← qNameType qName

    let qNameArity ∷ Nat
        qNameArity = arity def

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
                   incVarsEtaExpanded = map indexPlus1 argsEtaExpanded

                   newVar ∷ Arg Term
                   newVar = Arg NotHidden Relevant (Var 0 [])

               freshVar ← newTVar

               return $
                 Lam NotHidden
                     (Abs freshVar (Def qName (incVarsEtaExpanded ++ [newVar])))

             else do
               reportSLn "etaExpand" 20 $
                 "qname: " ++ show qName ++ "\n"++
                 "qNameArity: " ++ show qNameArity ++ "\n"++
                 "length args: " ++ show (length args)
               __IMPOSSIBLE__

  -- We don't know an example of eta-contraction with Con, therefore
  -- we don't do anything.
  etaExpand term@(Con _ _) = return term

  etaExpand (Fun tyArg ty) = liftM2 Fun (etaExpand tyArg) (etaExpand ty)

  etaExpand (Lam h (Abs x termAbs)) = fmap (Lam h . Abs x) (etaExpand termAbs)

  -- It seems it is not necessary to eta-expand the tyArg like in the
  -- case of Fun (Arg Type) Type.
  etaExpand (Pi tyArg (Abs x tyAbs)) = fmap (Pi tyArg . Abs x) (etaExpand tyAbs)

  etaExpand (Var n args) = fmap (Var n) (mapM etaExpand args)

  etaExpand DontCare    = __IMPOSSIBLE__
  etaExpand (Level _)   = __IMPOSSIBLE__
  etaExpand (Lit _)     = __IMPOSSIBLE__
  etaExpand (MetaV _ _) = __IMPOSSIBLE__
  etaExpand (Sort _)    = __IMPOSSIBLE__

instance EtaExpandible a ⇒ EtaExpandible (Arg a) where
  etaExpand (Arg h r t) = fmap (Arg h r) (etaExpand t)
