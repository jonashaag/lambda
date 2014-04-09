module Lambda where

import Control.Arrow ((>>>))


--- Utils ---
indent :: String -> String -> String
indent prefix = unlines . map (prefix ++) . lines

-- | If 'check' gives us an error message, display it. Otherwise, 'continue'.
maybeError :: (a -> Maybe String) -> (a -> b) -> a -> b
maybeError check continue x = case check x of
  Just msg -> error msg
  Nothing  -> continue x


--- | Lambda calculus ---
type DeBruijnIdx = Int

-- | Lambda calculus simplified to using only De Bruijn Indices.
data DeBruijnLambda = DInt Int
                    | DVar DeBruijnIdx
                    | DAbstr DeBruijnLambda
                    | DApp DeBruijnLambda DeBruijnLambda

instance Show DeBruijnLambda where
  show (DInt i) = show i
  show (DVar n) = "[" ++ show n ++ "]"
  show (DAbstr body) = "(λ\n" ++ indent "  " (show body) ++ ")"
  show (DApp abstr@(DApp _ _) expr) = "(" ++ show abstr ++ ") " ++ show expr
  show (DApp abstr expr) = show abstr ++ " " ++ show expr


-- | Original lambda calculus with single-argument abstraction and application.
--   Also supports De Bruijn Indices since this data structure is used during
--   the de-bruijnification (see 'deBruijnify').
data SimpleLambda = SInt Int
                  | SVar String
                  | SDeBruijnVar DeBruijnIdx
                  | SAbstr String SimpleLambda
                  | SDeBruijnAbstr SimpleLambda
                  | SApp SimpleLambda SimpleLambda
                  --deriving Show

instance Show SimpleLambda where
  show (SInt i) = show i
  show (SVar s) = s
  show (SDeBruijnVar n) = "[" ++ show n ++ "]"
  show (SAbstr name body) = "(λ " ++ name ++ " -> \n" ++ indent "  " (show body) ++ ")"
  show (SDeBruijnAbstr body) = "(λ\n" ++ indent "  " (show body) ++ ")"
  show (SApp abstr@(SApp _ _) expr) = "(" ++ show abstr ++ ") " ++ show expr
  show (SApp abstr expr) = show abstr ++ " " ++ show expr


-- | Highish-level lambda calculus that supports multi-argument abstraction
--   and application, 'let ... in ...' and '... where ...'.
data NiceLambda = Int Int
                | Var String
                | Abstr [String] NiceLambda
                | App NiceLambda [NiceLambda]
                | Let [(String,NiceLambda)] NiceLambda
                | Where NiceLambda [(String,NiceLambda)]
                deriving Show


checkSyntax :: NiceLambda -> Maybe String
checkSyntax (App body args) = case body of
  Abstr _ _ -> Nothing
  otherwise -> Just $ "Cannot apply " ++ show args ++ " to non-abstraction " ++ show body
checkSyntax _ = Nothing


-- | λx,y.z  =>  λx.λy.z
--   e x y   =>  (e x) y
translateMultiArg :: NiceLambda -> SimpleLambda
translateMultiArg (Var s)  = SVar s
translateMultiArg (Int i) = SInt i
translateMultiArg (Abstr [name] body)
  = SAbstr name (translateMultiArg body)
translateMultiArg (Abstr (name:restNames) body)
  = translateMultiArg $ Abstr [name] (Abstr restNames body)
translateMultiArg (App abstr [arg])
  = SApp (translateMultiArg abstr) (translateMultiArg arg)
translateMultiArg (App abstr (arg:restArgs))
  = translateMultiArg $ App (App abstr [arg]) restArgs


-- | let foo = bar in expr  =>  (λfoo.expr) bar
--   expr where foo = bar   =>  (λfoo.expr) bar
translateLet :: NiceLambda -> NiceLambda
translateLet (Let definitions inExpr)    = App (Abstr defNames (translateLet inExpr)) defExprs
  where
    (defNames,defExprs') = unzip definitions
    defExprs = map translateLet defExprs'
translateLet (Where inExpr definitions)  = translateLet $ Let definitions inExpr
translateLet otherwise_ = otherwise_


-- | Replaces bound variable names with De Bruijn Indices.
--   Free variables are left untouched.
deBruijnify :: SimpleLambda -> SimpleLambda
deBruijnify (SAbstr name body) = SDeBruijnAbstr $ deBruijnifyAbstr 1 (deBruijnify body)
  where 
    deBruijnifyAbstr nesting (SVar name') | name == name'
      = SDeBruijnVar nesting
    deBruijnifyAbstr nesting (SAbstr name' body) | name /= name'
      = SAbstr name' $ deBruijnifyAbstr (nesting + 1) body
    deBruijnifyAbstr nesting (SDeBruijnAbstr body)
      = SDeBruijnAbstr $ deBruijnifyAbstr (nesting + 1) body
    deBruijnifyAbstr nesting (SApp abstr arg) = SApp (deBruijnifyAbstr nesting abstr)
                                                     (deBruijnifyAbstr nesting arg)
    deBruijnifyAbstr _ otherwise_ = otherwise_
deBruijnify (SApp abstr arg) = SApp (deBruijnify abstr) (deBruijnify arg)
deBruijnify otherwise_ = otherwise_

extractDeBruijnLambda :: SimpleLambda -> DeBruijnLambda
extractDeBruijnLambda (SInt i)         = DInt i
extractDeBruijnLambda (SDeBruijnVar n) = DVar n
extractDeBruijnLambda (SDeBruijnAbstr body) = DAbstr $ extractDeBruijnLambda body
extractDeBruijnLambda (SApp abstr arg) = DApp (extractDeBruijnLambda abstr)
                                              (extractDeBruijnLambda arg)
extractDeBruijnLambda (SVar name) = error $ "Undefined name " ++ show name


process :: NiceLambda -> SimpleLambda
process = maybeError checkSyntax $ translateLet
                                   >>> translateMultiArg
                                   >>> deBruijnify


example1 = App (Var "square") [Int 5]
           `Where` [("square", Abstr ["x"] (App (Var "*") [Var "x", Var "x"]))]
