------------------------------------------------------------------------------
-- Eta expansion of Agda internal types
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.EtaExpansion ( EtaExpandible(etaExpand) ) where

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
import AgdaLib.Syntax.DeBruijn ( increaseByOneVar )
import Monad.Base              ( newTVar, pushTVar, T )

#include "../undefined.h"

------------------------------------------------------------------------------

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

    let newVar ∷ Arg Term
        newVar = Arg NotHidden Relevant (Var 0 [])

    freshVar ← newTVar
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
               pushTVar freshVar
               -- Because we are going to add a new abstraction, we
               -- need increase by one the numbers associated with the
               -- variables in the arguments.
               let incVarsEtaExpanded ∷ Args
                   incVarsEtaExpanded = map increaseByOneVar argsEtaExpanded
               return $
                 Lam NotHidden
                     (Abs freshVar (Def qName (incVarsEtaExpanded ++ [newVar])))

             else __IMPOSSIBLE__

  -- We don't know an example of eta-contraction with Con, therefore
  -- we don't do anything.
  etaExpand term@(Con _ _) = return term

  etaExpand (Fun tyArg ty) = liftM2 Fun (etaExpand tyArg) (etaExpand ty)

  etaExpand (Lam h (Abs x termAbs)) = do
    pushTVar x
    fmap (Lam h . Abs x) (etaExpand termAbs)

  -- It seems it is not necessary to eta-expand the tyArg like in the
  -- case of Fun (Arg Type) Type.
  etaExpand (Pi tyArg (Abs x tyAbs)) = do
    pushTVar x
    fmap (Pi tyArg . Abs x) (etaExpand tyAbs)

  etaExpand (Var n args) = fmap (Var n) (mapM etaExpand args)

  etaExpand DontCare    = __IMPOSSIBLE__
  etaExpand (Level _)   = __IMPOSSIBLE__
  etaExpand (Lit _)     = __IMPOSSIBLE__
  etaExpand (MetaV _ _) = __IMPOSSIBLE__
  etaExpand (Sort _)    = __IMPOSSIBLE__

instance EtaExpandible a ⇒ EtaExpandible (Arg a) where
  etaExpand (Arg h r t) = fmap (Arg h r) (etaExpand t)
