------------------------------------------------------------------------------
-- Eta expansion of Agda internal types
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.EtaExpansion ( etaExpand ) where

-- Haskell imports

-- import Control.Monad
-- import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.State ( evalState, get, put )

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
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports

import AgdaLib.Interface ( qNameType )
import AgdaLib.Syntax.DeBruijn ( increaseByOneVar )
import Common ( AllDefinitions, T )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------

class EtaExpandible a where
    etaExpand :: AllDefinitions → a → T a

instance EtaExpandible Type where
    etaExpand allDefs (El (Type (Lit (LitLevel r n))) term)
        | n `elem` [ 0, 1 ] =
            do termEtaExpanded ← etaExpand allDefs term
               return $ El (Type (Lit (LitLevel r n))) termEtaExpanded
        | otherwise = __IMPOSSIBLE__

    etaExpand _ _ = __IMPOSSIBLE__

instance EtaExpandible Term where
    etaExpand allDefs (Def qName args) = do
      vars ← lift get

      let qNameArity :: Nat
          qNameArity = arity $ qNameType allDefs qName

      argsEtaExpanded ← mapM (etaExpand allDefs) args

      let newVar :: Arg Term
          newVar = Arg NotHidden Relevant (Var 0 [])

      let freshVar :: String
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
                 lift $ put $ freshVar : vars
                 -- Because we are going to add a new abstraction, we
                 -- need increase by one the numbers associated with the
                 -- variables in the arguments.
                 let incVarsEtaExpanded :: Args
                     incVarsEtaExpanded = map increaseByOneVar argsEtaExpanded
                 return $
                   Lam NotHidden (Abs freshVar
                                      (Def qName
                                           (incVarsEtaExpanded ++ [newVar])))
               else __IMPOSSIBLE__

    -- We don't know an example of eta-contraction with Con, therefore we
    -- don't do anything.
    etaExpand _ term@(Con _ _ ) = return term

    etaExpand allDefs (Fun tyArg ty) = do
      tyArgEtaExpanded ← etaExpand allDefs tyArg
      tyEtaExpanded    ← etaExpand allDefs ty
      return $ Fun tyArgEtaExpanded tyEtaExpanded

    etaExpand allDefs (Lam h (Abs x termAbs)) = do
      -- We add the variable x to the enviroment.
      vars ← lift get
      lift $ put $ x : vars

      termAbsEtaExpanded ← etaExpand allDefs termAbs
      return $ Lam h (Abs x termAbsEtaExpanded)

    -- It seems it is not necessary to eta-expand the tyArg like in the
    -- case of Fun (Arg Type) Type.
    etaExpand allDefs (Pi tyArg (Abs x tyAbs)) = do
      -- We add the variable x to the enviroment.
      vars ← lift get
      lift $ put $ x : vars

      tyAbsEtaExpanded ← etaExpand allDefs tyAbs
      return $ Pi tyArg (Abs x tyAbsEtaExpanded)

    etaExpand allDefs (Var n args) = do
      argsEtaExpanded ← mapM (etaExpand allDefs) args
      return $ Var n argsEtaExpanded

    etaExpand _ DontCare     = __IMPOSSIBLE__
    etaExpand _ (Lit _ )     = __IMPOSSIBLE__
    etaExpand _ (MetaV _ _ ) = __IMPOSSIBLE__
    etaExpand _ (Sort _ )    = __IMPOSSIBLE__

instance EtaExpandible a => EtaExpandible (Arg a) where
    etaExpand allDefs (Arg h r t) = do
      tEtaExpanded ← etaExpand allDefs t
      return (Arg h r tEtaExpanded)
