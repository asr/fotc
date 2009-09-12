-- Adapted from agdaLight (Plugins.FOL.Substitution).

module FOL.Substitution where

import FOL.Types

{-| Formula substitution. -}

substFormula :: String -> FOLTerm -> Formula -> Formula
substFormula v t p =
    case p of
        Predicate s ts  -> Predicate s (map (substTerm v t) ts)
        And p1 p2       -> And (substFormula v t p1) (substFormula v t p2)
        Or p1 p2        -> Or (substFormula v t p1) (substFormula v t p2)
        Not q           -> Not (substFormula v t q)
        Implies p1 p2   -> Implies (substFormula v t p1) (substFormula v t p2)
        Equiv p1 p2     -> Equiv (substFormula v t p1) (substFormula v t p2)
        ForAll s f      -> ForAll s (\x -> substFormula v t (f x))
        Exists s f      -> Exists s (\x -> substFormula v t (f x))
        TRUE            -> TRUE
        FALSE           -> FALSE

substTerm :: String -> FOLTerm -> FOLTerm -> FOLTerm
substTerm v t1 t2 =
    case t2 of
        FOLFun s ts             -> FOLFun s (map (substTerm v t1) ts)
        FOLVar s    | s == v    -> t1
                    | otherwise -> t2
