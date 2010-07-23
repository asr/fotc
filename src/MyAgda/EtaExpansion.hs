------------------------------------------------------------------------------
-- Eta expansion of Agda internal terms
------------------------------------------------------------------------------

module MyAgda.EtaExpansion ( etaExpandType ) where

-- Haskell imports
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.State ( evalState, get, StateT, put )

-- Agda library imports
-- import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common ( Arg(Arg), Hiding(NotHidden), Nat )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , Args
    , arity
    , Term(Def, Con, Fun, Lam, Lit, MetaV, Pi, Sort, Var)
    , Sort(Type)
    , Type(El)
    )
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import Common ( Vars )
import MyAgda.Interface ( getQNameInterface, getQNameType )
import MyAgda.Syntax.Internal ( incTermVariables )
import Utils.Names ( freshName )

#include "../undefined.h"

------------------------------------------------------------------------------

-- The eta-expansion monad.
type EE = StateT Vars IO

etaExpandArgTerm :: Arg Term -> EE (Arg Term)
etaExpandArgTerm (Arg h term) = do
  termEtaExpanded <- etaExpandTerm term
  return (Arg h termEtaExpanded)

etaExpandArgType :: Arg Type -> EE (Arg Type)
etaExpandArgType (Arg h ty) = do
  typeEtaExpanded <- etaExpandType ty
  return (Arg h typeEtaExpanded)

etaExpandTerm :: Term -> EE Term
etaExpandTerm (Def qName args) = do

  vars <- get

  interface <- liftIO $ getQNameInterface qName

  let qNameArity :: Nat
      qNameArity = arity $ getQNameType interface qName

  argsEtaExpanded <- mapM etaExpandArgTerm args

  let newVar :: Arg Term
      newVar = Arg NotHidden (Var 0 [])

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
               put (freshVar : vars)
               -- Because we are going to add a new abstraction, we
               -- need increase by one the numbers associated with the
               -- variables in the arguments.
               let incVarsEtaExpanded :: Args
                   incVarsEtaExpanded = map incTermVariables argsEtaExpanded
               return $
                  Lam NotHidden (Abs freshVar
                                     (Def qName
                                          (incVarsEtaExpanded ++ [newVar])))
             else __IMPOSSIBLE__

-- We don't know an example of eta-contraction with Con, therefore we
-- don't do anything.
etaExpandTerm term@(Con _ _) = return term

etaExpandTerm (Fun tyArg ty) = do
  tyArgEtaExpanded <- etaExpandArgType tyArg
  tyEtaExpanded    <- etaExpandType ty
  return $ Fun tyArgEtaExpanded tyEtaExpanded

etaExpandTerm (Lam h (Abs name termAbs)) = do
  -- We add the variable 'name' to the enviroment.
  vars <- get
  put (name : vars)

  termAbsEtaExpanded <- etaExpandTerm termAbs
  return $ Lam h (Abs name termAbsEtaExpanded)

-- It seems it is not necessary to eta-expand the tyArg like in the
-- case of Fun (Arg Type) Type.
etaExpandTerm (Pi tyArg (Abs name tyAbs)) = do
  -- We add the variable 'name' to the enviroment.
  vars <- get
  put (name : vars)

  tyAbsEtaExpanded <- etaExpandType tyAbs
  return $ Pi tyArg (Abs name tyAbsEtaExpanded)

etaExpandTerm (Var n args) = do
  argsEtaExpanded <- mapM etaExpandArgTerm args
  return $ Var n argsEtaExpanded

etaExpandTerm (Lit _)     = __IMPOSSIBLE__
etaExpandTerm (MetaV _ _) = __IMPOSSIBLE__
etaExpandTerm (Sort _)    = __IMPOSSIBLE__

etaExpandType :: Type -> EE Type
etaExpandType (El (Type (Lit (LitLevel r n))) term)
    | n `elem` [ 0, 1 ] =
        do termEtaExpanded <- etaExpandTerm term
           return $ El (Type (Lit (LitLevel r n))) termEtaExpanded
    | otherwise = __IMPOSSIBLE__
etaExpandType _ = __IMPOSSIBLE__
