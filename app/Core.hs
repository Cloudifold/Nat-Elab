{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}
module Core where

import Debug.Trace ( trace )

import Control.Applicative hiding (many, some)
import Control.Monad ( guard, Monad((>>=)), unless )
import Data.Char ( isAlphaNum )
import Data.Void
import System.Environment ( getArgs )
import System.Exit ( exitSuccess )
import Text.Megaparsec
    ( getSourcePos,
      parse,
      errorBundlePretty,
      initialPos,
      unPos,
      some,
      Parsec,
      MonadParsec(eof, takeWhile1P, try),
      SourcePos(SourcePos) )
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

import Text.Printf
import Prelude hiding (lookup)




-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

type Name = String

data Raw
  = RVar Name -- x
  | RLam Name Raw -- \x. t                            -- let f : A -> B = \x -> ....
  | RApp Raw Raw -- t u
  | RTop
  | RUnit
  | RTt
  | RFf
  | RTwo
  | REmpty
  | REmptyElim Raw
  | RIf Raw Raw Raw -- if x t u
  | RTyIf Raw Raw Raw -- if x t u
  | RU -- U
  | RPi Name Raw Raw -- (x : A) -> B
  | RLet Name Raw Raw Raw -- let x : A = t in u
  | RSrcPos SourcePos Raw -- source position for error reporting
  deriving (Show)

{-

-}

type Type = Term

data Term
  = Var Ix
  | Lam Name Term
  | App Term Term
  | Top
  | Unit
  | Tt
  | Ff
  | Empty
  | EmptyElim Term
  | Two
  | If Term Term Term
  | TyIf Term Term Term
  | U
  | Pi Name Type Type
  | Let Name Type Term Term


{-
    Theory :

    ctxt , x : A |- , t(x) : B
    -----------------
    ctxt |- Lam x t : A -> B

    ctxt |- u : A , t : A -> B
    ----------------
    ctxt |- App t u : B

    ctxt , x : A |- t(x) : B    ctxt |- u : A
    ----------------
    ctxt |- App (Lam x t) u = t(u) : B

    ctxt , x : A |- B(x) : U
    ----------------
    ctxt |- Pi x A B : U

    ctxt |- A : U , B : U
    -----------------
    ctxt , x : Two |- If x A B : U

    ctxt , t : A , u : B
    ----------------
    If x t u |- Pi x Two (If x A B) : U

    ctxt , x : A |- t(x) : B(x)
    ----------------
    ctxt |- Lam x t(x) : Pi x A B

    ctxt |- t : Pi x A B , u : A
    ----------------
    ctxt |- App t u : B(u)

    ctxt , x : A |- t(x) : B(x)    ctxt |- u : A
    ----------------
    ctxt |- App (Lam x t) u = t(u) : B(u)



    ctxt , x : A |- B(x) : U
    ----------------
    ctxt |- W x A B : U

    ctxt |- u : A , t : Pi y B(u) (W x A B)
    ----------------
    ctxt |- Sup u t : W x A B


    ctxt , w : W x A B |- C(w) : U
    ctxt |- w : W x A B 
    ctxt , u : A , t : Pi y B(u) (W x A B) , v : Pi z B(u) C(u(z)) |-  c(u,t,v) : C(Sup u t)
    ----------------
    ctxt |- Wrec w c(u,t,v) : C(w)

    ctxt |- u : A , t : Pi y B(u) (W x A B)
    ctxt , w : W x A B |- C(w) : U
    ctxt , u : A , t : Pi y B(u) (W x A B) , v : Pi z B(u) C(t(z)) |-  c(u,t,v) : C(Sup u t)
    ----------------
    ctxt |- Wrec (Sup u t) c = c(u, t, (Lam z (Wrec t(z) c))) : C(Sup u t)

-}

type Env = [Val]

data Closure = Closure Env Term
  deriving Show

type VTy = Val

-- Neutral Terms and Values
data Val
  = VVar Lvl
  | VApp Val ~Val
  | VTop
  | VUnit
  | VEmpty
  | VEmptyElim ~Val
  | VTt
  | VFf
  | VTwo
  | VIf ~Val ~Val ~Val
  | VTyIf ~Val ~Val ~Val
  | VLam Name {-# UNPACK #-} Closure
  | VPi Name ~VTy {-# UNPACK #-} Closure
  | VU
  deriving (Show)

{-
  | VW  Name ~VTy {-# UNPACK #-} Closure
  | VSup Val ~Val
-}

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (u : env) t

eval :: Env -> Term -> Val
eval env t = case t of
  Var (Ix x) -> env !! x
  App t u -> case (eval env t, eval env u) of
    (VLam _ t, u) -> t $$ u
    (VPi _ a b, t) ->  b $$ t
    (t, u) -> VApp t u
  Top  -> VTop
  Unit -> VUnit
  EmptyElim t -> VEmptyElim (eval env t)
  Empty -> VEmpty
  Tt -> VTt
  Ff -> VFf
  Two -> VTwo
  If x a b -> case (eval env x) of
    VTt -> (eval env a)
    VFf -> (eval env b)
    _   -> VIf (eval env x) (eval env a) (eval env b)
  TyIf x a b -> case (eval env x) of
    VTt -> (eval env a)
    VFf -> (eval env b)
    _   -> VTyIf (eval env x) (eval env a) (eval env b)
  Lam x t -> VLam x (Closure env t)
  Pi x a b -> VPi x (eval env a) (Closure env b)
  Let x _ t u -> eval (eval env t : env) u
  U -> VU

{-
  Sup u t -> VSup (eval env u) (eval env t)
  Wrec w u t v c -> VWrec (eval env w) u t v (Closure env c)
-}

--   context length   level  index
lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

--      length
quote :: Lvl -> Val -> Term
quote l v = case v of
  VVar x -> Var (lvl2Ix l x)
  VApp a b -> App (quote l a) (quote l b)
  VLam s clo -> Lam s (quote (l+1) (clo $$ VVar l))
  VPi s ty clo -> Pi s (quote l ty) (quote (l+1) (clo $$ VVar l))
  VTop  -> Top
  VUnit -> Unit
  VTt -> Tt
  VFf -> Ff
  VTwo -> Two
  VIf x t u -> If (quote l x) (quote l t) (quote l u)
  VTyIf x t u -> TyIf (quote l x) (quote l t) (quote l u)
  VU -> U
  VEmpty -> Empty
  VEmptyElim t -> EmptyElim (quote l t)

{- VW s ty clo  -> W s (quote l ty) (quote (l+1) (clo $$ VVar l))
  VSup u t -> Sup (quote l u) (quote l t)
  VWrec w u t v clo -> Wrec (quote l w) u t v (quote (l+1) (clo $$ VVar l))
  -}

normalform :: Env -> Term -> Term
normalform env t = quote (Lvl (length env)) (eval env t)

-- | Beta-eta conversion checking.
--   Conversion checking works on Val. We do *not* compare Term for equality!
--   Alternative solution: Val ->(nf)-> Term , then compare Term
--      (worse performance, eta conversion checking is difficult)
--
--   Precondition: both values have the same type
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (t, u) of
  (VU, VU) -> True
  (VUnit, VUnit) -> True
  (VTop, VTop) -> True
  (VFf, VFf) -> True
  (VTt, VTt) -> True
  (VTwo, VTwo) -> True
  (VEmpty, VEmpty) -> True
  (VEmptyElim v, _) -> True
  (_, VEmptyElim v) -> True
  (VIf x a b, VIf x' a' b') -> conv l a a' && conv l b b' && conv l x x'
  (VTyIf x a b, VTyIf x' a' b') -> conv l a a' && conv l b b' && conv l x x'
  (VPi _ a b, VPi _ a' b') ->
    conv l a a'
      && conv (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VLam _ t, VLam _ t') ->
    conv (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (VLam _ t, u) ->
    conv (l + 1) (t $$ VVar l) (VApp u (VVar l))
  (u, VLam _ t) ->
    conv (l + 1) (VApp u (VVar l)) (t $$ VVar l)
  (VVar x, VVar x') -> x == x'
  (VApp t u, VApp t' u') -> conv l t t' && conv l u u'
  _ -> False

{-
  (VW _ a b, VW _ a' b') ->
    conv l a a'
      && conv (l + 1) (b $$ VVar l) (b' $$ VVar l)
  -}

-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, VTy)]

-- | Elaboration context.
data Ctxt = Ctxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

-- "unzipped" Ctxt definition, for performance reason (also for convenience)

emptyCxt :: SourcePos -> Ctxt
emptyCxt = Ctxt [] [] 0

-- | Extend Cxt with a bound variable.
bind :: Name -> VTy -> Ctxt -> Ctxt
bind x ~a (Ctxt env types l pos) =
  Ctxt (VVar l:env) ((x, a):types) (l + 1) pos

define :: Name -> Val -> VTy -> Ctxt -> Ctxt
define x ~t ~a (Ctxt env types l pos) =
  Ctxt (t : env) ((x, a) : types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

report :: Ctxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

showVal :: Ctxt -> Val -> String
showVal cxt v = prettyTerm 0 (map fst (types cxt)) (quote (lvl cxt) v) []

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x
  | x `elem` ns = fresh ns (x ++ "'")
  | otherwise = x

-- bidirectional algorithm:
--   use check when the type is already known
--   use infer if the type is unknown
check :: Ctxt -> Raw -> VTy -> M Term
check ctxt t a = case (t, a) of
  -- set source pos
  (RSrcPos pos t, a) -> check (ctxt {pos = pos}) t a
  -- check Lam with Pi
  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a ctxt) t (b $$ VVar (lvl ctxt))
  (RLet x a t u, a') -> do
    a <- check ctxt a VU
    let ~va = eval (env ctxt) a
    t <- check ctxt t va
    let ~vt = eval (env ctxt) t
    u <- check (define x vt va ctxt) u a'
    pure (Let x a t u)

  (REmptyElim t, a) -> do
    t <- check ctxt t VEmpty
    pure (EmptyElim t)
  _ -> do
    (t, tty) <- infer ctxt t
    unless (conv (lvl ctxt) tty a) $
      report ctxt
          (printf
          "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
          (showVal ctxt a) (showVal ctxt tty)) 
    pure t

infer :: Ctxt -> Raw -> M (Term, VTy)
infer ctxt = \case
  RVar x -> do
    let go i [] = report ctxt ("variable out of scope: " ++ x)
        go i ((x', a):tys)
          | x == x'   = pure (Var i, a)
          | otherwise  = go (i+1) tys
    go 0 (types ctxt)

  RLam s raw -> report ctxt $ "Cannot infer type for lambda expression"
  RApp t u -> do
    (t, tty) <- infer ctxt t
    case tty of
      VPi s a clo -> do
        u <- check ctxt u a
        pure (App t u, clo $$ eval (env ctxt) u)
      tty -> report ctxt $ "Expect a function type, instead inferred:\n\n  " ++ showVal ctxt tty
  RU -> pure (U, VU)
  RTop -> pure (Top, VUnit)
  RUnit -> pure (Unit, VU)
  RFf  -> pure (Ff, VTwo)
  RTt  -> pure (Tt, VTwo)
  RTwo -> pure (Two, VU)
  RPi x a b -> do
    a <- check ctxt a VU
    let va = (eval (env ctxt) a)
    b <- check (bind x va ctxt) b VU
    pure (Pi x a b, VU)
  RTyIf x t u -> do
    (x, c) <- infer ctxt x
    (t, a) <- infer ctxt t
    (u, b) <- infer ctxt u
    (case conv (lvl ctxt) a VU && conv (lvl ctxt) b VU of
      True -> if conv (lvl ctxt) c VTwo
        then pure (TyIf x t u, VU)
        else report ctxt
          (printf
            "Two type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal ctxt VTwo) (showVal ctxt c))
      False -> report ctxt
          (printf
            "%s and %s should both be types instead of terms \n"
            (showVal ctxt a) (showVal ctxt b)))
  RIf x t u -> do
    (x, c) <- infer ctxt x
    (t, a) <- infer ctxt t
    (u, b) <- infer ctxt u
    (if conv (lvl ctxt) c VTwo
      then if conv (lvl ctxt) a b
        then pure (If x t u, a)
        else pure (If x t u, VTyIf (eval (env ctxt) x) a b)
      else report ctxt
        (printf
          "Two type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
          (showVal ctxt VTwo) (showVal ctxt c)))
      
  REmpty -> pure (Empty, VU)
  REmptyElim t -> report ctxt $ "Cannot infer type for EmptyElim"

  RLet x a t u -> do
    a <- check ctxt a VU
    let ~va = eval (env ctxt) a
    t <- check ctxt t va
    let ~vt = eval (env ctxt) t
    (u, uty) <- infer (define x vt va ctxt) u
    pure (Let x a t u, uty)
  
  RSrcPos sp t -> infer (ctxt {pos = sp}) t


-- printing precedences
atomp = 4 :: Int -- U, var
appp = 3 :: Int -- application
wp   = 2 :: Int -- W, wrec, sup
pip = 1 :: Int -- pi
letp = 0 :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTerm :: Int -> [Name] -> Term -> ShowS
prettyTerm prec = go prec
  where
    piBind ns x a =
      showParen True ((x ++) . (" : " ++) . go letp ns a)
    goPi ns (Pi "_" a b) =
      (" -> " ++) . go appp ns a . (" -> " ++) . go pip ("_" : ns) b
    goPi ns (Pi (fresh ns -> x) a b) =
      piBind ns x a . goPi (x : ns) b
    goPi ns b =
      (" -> " ++) . go pip ns b

    go :: Int -> [Name] -> Term -> ShowS
    go p ns = \case
      Var (Ix x) -> ((ns !! x) ++)
      App t u -> par p appp $ go appp ns t . (' ' :) . go atomp ns u
      Lam (fresh ns -> x) t -> par p letp $ ("\\ " ++) . (x ++) . goLam (x : ns) t
        where
          goLam ns (Lam (fresh ns -> x) t) =
            (' ' :) . (x ++) . goLam (x : ns) t
          goLam ns t =
            (" . " ++) . go letp ns t
      U -> ("U" ++)
      Top -> ("top" ++)
      Ff -> ("f" ++)
      Tt -> ("t" ++)
      Unit -> ("Unit" ++)
      Empty -> ("Empty" ++)
      EmptyElim t -> ("EmptyElim " ++) . go p ns t
      Two -> ("Two" ++)
      If x t u -> ("If " ++) . go p ns x . (", " ++) . go p ns t . (", " ++) . go p ns u
      TyIf x t u -> ("TyIf " ++) . go p ns x . (", " ++) . go p ns t . (", " ++) . go p ns u
      Pi "_" a b -> par p pip $ go appp ns a . (" -> " ++) . go pip ("_" : ns) b
      Pi (fresh ns -> x) a b -> par p pip $ piBind ns x a . goPi (x : ns) b
      Let (fresh ns -> x) a t u ->
        par p letp $
          ("let " ++) . (x ++) . (" : " ++) . go letp ns a
            . ("\n    = " ++)
            . go letp ns t
            . ("\nin\n" ++)
            . go letp (x : ns) u


instance Show Term where showsPrec p = prettyTerm p []

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme = L.lexeme ws

symbol s = lexeme (C.string s)

char c = lexeme (C.char c)

parens p = char '(' *> p <* char ')'

pArrow = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in"
  || x == "λ" || x == "U"
  || x == "f" || x == "t"
  || x == "Unit" || x == "Two"
  || x == "EmptyElim" || x == "Empty" 
  || x == "top" || x == "if" || x == "TyIf"


pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
  withPos ((RVar <$> pIdent) <|> (RUnit <$ symbol "Unit") <|> (RU <$ symbol "U") <|> (RFf <$ symbol "f") <|> (RTt <$ symbol "t")
  <|> (RTwo <$ symbol "Two")  <|> (RTop <$ symbol "top")) 
  <|> (REmpty <$ symbol "Empty")
    <|> parens pRaw

pBinder = pIdent <|> symbol "_"

pSpine = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pEmptyElim = do
  symbol "EmptyElim"
  t <- pRaw
  pure (REmptyElim t)


pIf = do
  (x,a,b) <- ((,,) <$> (symbol "if" *> pRaw) <*> (symbol "," *> pRaw) <*> (symbol "," *> pRaw))
  pure (RIf x a b)

pTyIf = do
  (x,a,b) <- ((,,) <$> (symbol "TyIf" *> pRaw) <*> (symbol "," *> pRaw) <*> (symbol "," *> pRaw))
  pure (RTyIf x a b)



pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _ -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  pKeyword "in"
  RLet x a t <$> pRaw





pRaw = withPos (pLam <|> pLet <|> try pTyIf <|> try pIf  <|> try pPi
  <|> pEmptyElim <|> funOrSpine)

pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm <- parseString file
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n"  lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg =
  unlines
    [ "usage: inductive [--help|nf|type]",
      "  --help : display this message",
      "  nf     : read & typecheck expression from stdin, print its normal form and type",
      "  type   : read & typecheck expression from stdin, print its type"
    ]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ normalform [] t
          putStrLn "  :"
          print $ quote 0 a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> print $ quote 0 a
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode file = mainWith (pure [mode]) (do src <- readFile file; (,src) <$> parseString src)


