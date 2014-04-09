import qualified Data.Map as M
import qualified Data.MultiMap as MM
import Control.Arrow ((>>>))
import Control.Monad.State

import Lambda

data TypedDeBruijnLambda = TInt   Type Int
                         | TVar   Type DeBruijnIdx
                         | TAbstr Type TypedDeBruijnLambda
                         | TApp   Type TypedDeBruijnLambda TypedDeBruijnLambda
                         deriving Show

getType (TInt   t _) = t
getType (TVar   t _) = t
getType (TAbstr t _) = t
getType (TApp   t _ _) = t

data Type = TypeVar Int
          | Type :->: Type
          | Type String
          deriving (Ord, Eq, Show)


type Subst = MM.MultiMap Type Type
type SingleSubst = [(Type,Type)]


assignTypeVariables :: Subst -> DeBruijnLambda -> (Subst,TypedDeBruijnLambda)
assignTypeVariables subst lambda = evalState (assign subst lambda) 1
  where
    assign subst (DInt i)
      = do typeVar <- nextVar
           let tint = TInt typeVar i
               subst' = MM.insert typeVar (Type "Int") subst
           return (subst',tint)

    assign subst (DVar n)
      = do typeVar <- nextVar 
           return (subst,TVar typeVar n)

    assign subst (DAbstr body)
      = do typeVar <- nextVar
           (subst',body') <- assign subst body
           let argVars = map getType (findArgOccurences 1 body')

           -- TODO maybe simplify to "always add newVar + maybe add newVar -> someVar constraint"
           if null argVars then do
             newVar <- nextVar
             let subst'' = MM.insert typeVar (newVar :->: getType body') subst'
             return (subst'',TAbstr typeVar body')
           else
             let (someVar:restVars) = argVars
                 subst'' = foldl (\s x -> MM.insert x someVar s) subst' restVars
                 subst''' = MM.insert typeVar (someVar :->: getType body') subst''
             in return (subst''',TAbstr typeVar body')

    assign subst (DApp abstr arg)
      = do (subst' ,abstr') <- assign subst  abstr
           (subst'',arg')   <- assign subst' arg
           typeVar <- nextVar
           let subst''' = MM.insert (getType abstr') (getType arg' :->: typeVar) subst''
           return (subst''',TApp typeVar abstr' arg')

    findArgOccurences nesting x@(TVar t n) | n == nesting = [x]
                                           | otherwise    = []
    findArgOccurences nesting (TApp t abstr arg) = concatMap (findArgOccurences nesting) [abstr,arg]
    findArgOccurences nesting (TAbstr t body) = findArgOccurences (nesting + 1) body
    findArgOccurences _       (TInt _ _) = []

    nextVar
      = do c <- get
           put $ c + 1
           return $ TypeVar c

simplifySubst :: Subst -> SingleSubst
simplifySubst subst = concatMap unrollEquations (MM.assocs subst)
  where unrollEquations (k,[x]) = [(k,x)]
        unrollEquations (k,(x:xs)) = [(k,x)] ++ unrollEquations (x,xs)

unify :: SingleSubst -> SingleSubst
unify [] = []
unify ((t1,t2):subst')
  = if t1 == t2 then unify subst'
    else case (t1,t2) of
          ((t1In :->: t1Out), (t2In :->: t2Out))
            -> unify $ [(t1In,t2In), (t1Out,t2Out)] ++ subst'

          -- TODO Don't throw away constraint after using 'replaceTypeVar'.
          -- Types of inner/intermediate expressions might be of interest too.
          ((TypeVar n),_)
            -> (t1,t2) : (unify (map (replaceTypeVar n t2) subst'))
          (_,(TypeVar n))
            -> (t2,t1) : (unify (map (replaceTypeVar n t1) subst'))

          otherwise -> error $ "can't handle" ++ show (t1,t2)

replaceTypeVar n newType (t1,t2) = (replaceTypeVar' n newType t1,replaceTypeVar' n newType t2)
replaceTypeVar' n t2 (TypeVar n') | n == n' = t2
replaceTypeVar' n t2 (tIn :->: tOut) = replaceTypeVar' n t2 tIn :->: replaceTypeVar' n t2 tOut
replaceTypeVar' _ _  x = x


instance (Show k, Show a) => Show (MM.MultiMap k a) where
  show m = show (MM.toMap m)

x |> f = f x
f <| x = f x

example2 = DApp (DAbstr (DVar 1)) (DInt 5)

{-
TODO: Add support for let-polymorphism.

const (const 5) (const id) :: (t0 -> Int)
const1 :: t1 -> (t2 -> Int) 
const2 :: t3 -> Int
const3 :: t4 -> (t5 -> t6)
-}
example3 = App (Var "const") [App (Var "const") [Int 5],
                              App (Var "const") [Var "id"]]
           `Where` [("const", Abstr ["x", "y"] (Var "x"))
                   ,("id", Abstr ["x"] (Var "x"))]

onFst f (x,y) = (f x,y)
process2 = assignTypeVariables MM.empty >>> onFst (simplifySubst >>> unify)
