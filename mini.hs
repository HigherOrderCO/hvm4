-- Calculus of Interactions - Mini
-- ===============================
-- 
-- Term ::=
-- | Ref ::= "@" Name
-- | Var ::= Name
-- | Dp0 ::= Name "₀"
-- | Dp1 ::= Name "₁"
-- | Era ::= "&{}"
-- | Sup ::= "&" Name "{" Term "," Term "}"
-- | Dup ::= "!" Name "&" Name "=" Term ";"? Term
-- | Lam ::= "λ" Name "." Term
-- | App ::= "(" Term " " Term ")"
-- | Ctr ::= "#" Name "{" [Term] "}"
-- | Mat ::= "λ" "{" "#" Name ":" Term ";"? Term "}"
-- 
-- Where:
-- - `Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $`
-- - `[X]  ::= "" | X ","? [X]

{-# LANGUAGE BangPatterns #-}

import Control.Monad (forM_, when)
import Data.Bits (shiftL)
import Data.Char (isDigit)
import Data.IORef
import Data.List (foldl', elemIndex)
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

debug :: Bool
debug = False

-- Types
-- =====

type Lab  = Int
type Name = Int

data Term
  = Var !Name
  | Dp0 !Name
  | Dp1 !Name
  | Ref !Name
  | Nam !String
  | Dry !Term !Term
  | Era
  | Sup !Lab !Term !Term
  | Dup !Name !Lab !Term !Term
  | Lam !Name !Term
  | App !Term !Term
  | Ctr !Name ![Term]
  | Mat !Name !Term !Term
  deriving (Eq)

data Kind
  = VAR
  | DP0
  | DP1
  deriving (Enum)

data Book = Book (M.Map Name Term)

data Env = Env
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_sub_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name k
  show (Dp0 k)       = int_to_name k ++ "₀"
  show (Dp1 k)       = int_to_name k ++ "₁"
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = k
  show (Dry f x)     = show_app f [x]
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f [x]
  show (Ctr k args)  = "#" ++ int_to_name k ++ "{" ++ unwords (map show args) ++ "}"
  show (Mat k c d)   = "λ{#" ++ int_to_name k ++ ":" ++ show c ++ ";" ++ show d ++ "}"

show_app :: Term -> [Term] -> String
show_app (Dry f x) args = show_app f (x : args)
show_app (App f x) args = show_app f (x : args)
show_app f         args = "(" ++ unwords (map show (f : args)) ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

-- Name Encoding/Decoding
-- ======================

alphabet :: String
alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

alphabet_first :: String
alphabet_first = filter (`notElem` "_0123456789") alphabet

name_to_int :: String -> Int
name_to_int = foldl' (\acc c -> (acc `shiftL` 6) + idx c) 0
  where idx c = maybe (error "bad name char") id (elemIndex c alphabet)

int_to_name :: Int -> String
int_to_name 0 = "_"
int_to_name n = reverse (go n)
  where go 0 = ""
        go m = let (q,r) = m `divMod` 64 in alphabet !! r : go q

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

parse_name :: ReadP String
parse_name = lexeme $ do
  head <- satisfy (`elem` alphabet_first)
  tail <- munch (`elem` alphabet)
  return (head : tail)

parse_nam :: ReadP Term
parse_nam = do
  lexeme (char '^')
  choice
    [ do lexeme (char '('); f <- parse_term; x <- parse_term; lexeme (char ')'); return (Dry f x)
    , do k <- parse_name; return (Nam k)
    ]

parse_term :: ReadP Term
parse_term = do
  t <- choice [parse_nam, parse_term_base]
  skipSpaces
  return t

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam
  , parse_dup
  , parse_par
  , parse_sup
  , parse_era
  , parse_ctr
  , parse_mat
  , parse_ref
  , parse_var
  ]

parse_par :: ReadP Term
parse_par = do
  lexeme (char '(')
  t <- parse_term
  ts <- many parse_term
  lexeme (char ')')
  return (foldl' App t ts)

parse_lam :: ReadP Term
parse_lam = do
  lexeme (char 'λ')
  k <- parse_name
  lexeme (char '.')
  t <- parse_term
  return (Lam (name_to_int k) t)

parse_dup :: ReadP Term
parse_dup = do
  lexeme (char '!')
  k <- parse_name
  lexeme (char '&')
  l <- parse_name
  lexeme (char '=')
  v <- parse_term
  optional (lexeme (char ';'))
  t <- parse_term
  return (Dup (name_to_int k) (name_to_int l) v t)

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- parse_name
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_term
    optional (lexeme (char ','))
    b <- parse_term
    return (Sup (name_to_int l) a b)

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_ctr :: ReadP Term
parse_ctr = do
  lexeme (char '#')
  k <- parse_name
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    args <- sepBy parse_term (optional (lexeme (char ',')))
    return (Ctr (name_to_int k) args)

parse_mat :: ReadP Term
parse_mat = do
  lexeme (char 'λ')
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (char '#')
    k <- parse_name
    lexeme (char ':')
    c <- parse_term
    optional (lexeme (char ';'))
    d <- parse_term
    optional (lexeme (char ';'))
    return (Mat (name_to_int k) c d)

parse_ref :: ReadP Term
parse_ref = do
  lexeme (char '@')
  k <- parse_name
  return (Ref (name_to_int k))

parse_var :: ReadP Term
parse_var = do
  k <- parse_name
  let kid = name_to_int k
  choice
    [ string "₀" >> return (Dp0 kid)
    , string "₁" >> return (Dp1 kid)
    , return (Var kid)
    ]

parse_func :: ReadP (Name, Term)
parse_func = do
  lexeme (char '@')
  k <- parse_name
  lexeme (char '=')
  f <- parse_term
  return (name_to_int k, f)

parse_book :: ReadP Book
parse_book = do
  skipSpaces
  funcs <- many parse_func
  skipSpaces
  eof
  return $ Book (M.fromList funcs)

read_term :: String -> Term
read_term s = case readP_to_S (parse_term <* skipSpaces <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse"

read_book :: String -> Book
read_book s = case readP_to_S parse_book s of
  [(b, "")] -> b
  _         -> error "bad-parse"

-- WNF
-- ===

data Frame
  = FDp0   Name Lab
  | FDp1   Name Lab
  | FApp   Term
  | FAppF  Term
  deriving Show

type Stack = [Frame]

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

wnf_enter :: Env -> Stack -> Term -> IO Term

wnf_enter e s (Var k) = do
  wnf_sub VAR e s k

wnf_enter e s (Dp0 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub DP0 e s k

wnf_enter e s (Dp1 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub DP1 e s k

wnf_enter e s (App f x) = do
  wnf_enter e (FApp x : s) f

wnf_enter e s (Dup k l v t) = do
  make_dup e k l v
  wnf_enter e s t

wnf_enter e s (Ref k) = do
  wnf_ref e s k

wnf_enter e s f = do
  wnf_unwind e s f

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []      v = return v
wnf_unwind e (x : s) v = do
  case x of
    FApp a   -> wnf_app e s v a
    FAppF f  -> wnf_app_mat e s f v
    FDp0 k l -> wnf_dup e s v k l (Dp0 k)
    FDp1 k l -> wnf_dup e s v k l (Dp1 k)

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s $ case ki of
      VAR -> Var k
      DP0 -> Dp0 k
      DP1 -> Dp1 k

wnf_dup :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup e s v k l t = do
  case v of
    Era       -> wnf_dup_era e s v k l t
    Sup {}    -> wnf_dup_sup e s v k l t
    Lam {}    -> wnf_dup_lam e s v k l t
    Ctr {}    -> wnf_dup_ctr e s v k l t
    Mat {}    -> wnf_dup_mat e s v k l t
    Nam {}    -> wnf_dup_nam e s v k l t
    Dry {}    -> wnf_dup_dry e s v k l t
    _         -> wnf_unwind e s (Dup k l v t)

wnf_dup_nam :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_nam e s (Nam n) k _ t = wnf_dup_0 e s k (Nam n) t

wnf_dup_dry :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_dry e s (Dry vf vx) k l t = wnf_dup_2 e s k l t vf vx Dry

wnf_dup_0 :: Env -> Stack -> Name -> Term -> Term -> IO Term
wnf_dup_0 e s k v t = do
  inc_inters e
  subst DP0 e k v
  subst DP1 e k v
  wnf e s t

wnf_dup_2 :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> (Term -> Term -> Term) -> IO Term
wnf_dup_2 e s k l t v1 v2 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  (v2a, v2b) <- clone e l v2
  subst DP0 e k (c v1a v2a)
  subst DP1 e k (c v1b v2b)
  wnf e s t

wnf_dup_era :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_era e s Era k _ t = wnf_dup_0 e s k Era t

wnf_dup_sup :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_sup e s (Sup vl va vb) k l t
  | l == vl = do
      inc_inters e
      subst DP0 e k va
      subst DP1 e k vb
      wnf e s t
  | otherwise = do
      wnf_dup_2 e s k l t va vb (Sup vl)

wnf_dup_lam :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_lam e s (Lam vk vf) k l t = do
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst DP0 e k (Lam x0 g0)
  subst DP1 e k (Lam x1 g1)
  subst VAR e vk (Sup l (Var x0) (Var x1))
  wnf e s t

wnf_dup_ctr :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_ctr e s (Ctr cn args) k l t = do
  inc_inters e
  args_clones <- forM args (clone e l)
  let args0 = map fst args_clones
  let args1 = map snd args_clones
  subst DP0 e k (Ctr cn args0)
  subst DP1 e k (Ctr cn args1)
  wnf e s t
  where forM = flip mapM

wnf_dup_mat :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_mat e s (Mat mn mc md) k l t = wnf_dup_2 e s k l t mc md (Mat mn)

wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s f a = do
  case f of
    Era       -> wnf_app_era e s f a
    Sup {}    -> wnf_app_sup e s f a
    Lam {}    -> wnf_app_lam e s f a
    Mat {}    -> wnf_enter e (FAppF f : s) a
    Nam {}    -> wnf_app_nam e s f a
    Dry {}    -> wnf_app_dry e s f a
    _         -> wnf_unwind e s (App f a)

wnf_app_nam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_nam e s (Nam fk) v = wnf e s (Dry (Nam fk) v)

wnf_app_dry :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_dry e s (Dry ff fx) v = wnf e s (Dry (Dry ff fx) v)

wnf_app_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_era e s Era v = do
  inc_inters e
  wnf e s Era

wnf_app_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_sup e s (Sup fL fa fb) v = do
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

wnf_app_lam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_lam e s (Lam fx ff) v = do
  inc_inters e
  subst VAR e fx v
  wnf e s ff

wnf_app_mat :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_mat e s f@(Mat mn mc md) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    wnf_enter e s (Sup l (App f0 x) (App f1 y))
  Ctr cn args -> do
    inc_inters e
    if mn == cn
      then apply_args e s mc args
      else apply_args e s md args
  _ -> wnf_unwind e s (App f a)

apply_args :: Env -> Stack -> Term -> [Term] -> IO Term
apply_args e s f args = wnf_enter e (map FApp args ++ s) f

wnf_ref :: Env -> Stack -> Name -> IO Term
wnf_ref e s k = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- alloc e f
      wnf_enter e s g
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

-- Environment
-- ===========

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 1
  sub <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids sub dm

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (env_inters e)
  writeIORef (env_inters e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (env_new_id e)
  writeIORef (env_new_id e) (n + 1)
  return ((n `shiftL` 6) + 63)

taker :: IORef (IM.IntMap a) -> Int -> IO (Maybe a)
taker ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> do
      return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = taker (env_dup_map e) k

take_sub :: Kind -> Env -> Name -> IO (Maybe Term)
take_sub ki e k = taker (env_sub_map e) (k)

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

subst :: Kind -> Env -> Name -> Term -> IO ()
subst ki e k v = modifyIORef' (env_sub_map e) (IM.insert (k) v)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Dp0 k , Dp1 k)

clone_list :: Env -> Lab -> [Term] -> IO ([Term],[Term])
clone_list e l []       = return $ ([],[])
clone_list e l (x : xs) = do
  (x0  , x1 ) <- clone e l x
  (xs0 , xs1) <- clone_list e l xs
  return $ (x0 : xs0 , x1 : xs1)

-- Allocation
-- ==========

alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where
  go m (Var k) = return $ Var (IM.findWithDefault k k m)
  go m (Dp0 k) = return $ Dp0 (IM.findWithDefault k k m)
  go m (Dp1 k) = return $ Dp1 (IM.findWithDefault k k m)
  go _ Era     = return Era
  go m (Sup l a b) = Sup l <$> go m a <*> go m b
  go m (App f x) = App <$> go m f <*> go m x
  go m (Dup k l v t) = do
    k' <- fresh e
    v' <- go m v
    t' <- go (IM.insert k k' m) t
    return $ Dup k' l v' t'
  go m (Lam k f) = do
    k' <- fresh e
    f' <- go (IM.insert k k' m) f
    return $ Lam k' f'
  go m (Ctr k args) = Ctr k <$> mapM (go m) args
  go m (Mat k c d) = Mat k <$> go m c <*> go m d
  go m (Ref k) = return (Ref k)
  go m (Nam k) = return (Nam k)
  go m (Dry f x) = Dry <$> go m f <*> go m x

-- Normalization
-- =============

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x' <- wnf e [] x
  case x' of
    Var k -> return $ Var k
    Dp0 k -> return $ Dp0 k
    Dp1 k -> return $ Dp1 k
    Era   -> return $ Era
    Sup l a b -> Sup l <$> snf e d a <*> snf e d b
    Dup k l v t -> do
      subst DP0 e k (Nam (int_to_name d ++ "₀"))
      subst DP1 e k (Nam (int_to_name d ++ "₁"))
      v' <- snf e d v
      t' <- snf e (d + 1) t
      return $ Dup d l v' t'
    Lam k f -> do
      subst VAR e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'
    App f x -> App <$> snf e d f <*> snf e d x
    Ctr k args -> Ctr k <$> mapM (snf e d) args
    Mat k c d' -> Mat k <$> snf e d c <*> snf e d d'
    Ref k -> return (Ref k)
    Nam k -> return (Nam k)
    Dry f x -> Dry <$> snf e d f <*> snf e d x

-- Collapsing
-- ==========

collapse :: Env -> Term -> IO Term
collapse e x = do
  !x <- wnf e [] x
  case x of
    Era -> return Era
    Sup l a b -> Sup l <$> collapse e a <*> collapse e b
    Lam k f -> do
      fV <- fresh e
      f' <- collapse e f
      inject e (Lam fV (Lam k (Var fV))) [f']
    App f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Ctr k args -> do
      argsVs <- mapM (\_ -> fresh e) args
      args'  <- mapM (collapse e) args
      let body = Ctr k (map Var argsVs)
      let lam  = foldr Lam body argsVs
      inject e lam args'
    Mat k c d -> do
      cV <- fresh e
      dV <- fresh e
      c' <- collapse e c
      d' <- collapse e d
      inject e (Lam cV (Lam dV (Mat k (Var cV) (Var dV)))) [c',d']
    Nam k -> return (Nam k)
    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    x -> return x

inject :: Env -> Term -> [Term] -> IO Term
inject e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    Sup l a b -> do
      (f0  , f1 ) <- clone e l f
      (xs0 , xs1) <- clone_list e l xs
      a' <- inject e f0 (a : xs0)
      b' <- inject e f1 (b : xs1)
      return $ Sup l a' b'
    x' -> inject e (App f x') xs
inject e f [] = return f

-- Tests
-- =====

book :: String
book = unlines
  [ "@T   = λt. λf. t"
  , "@F   = λt. λf. f"
  , "@NOT = λb. λt. λf. (b f t)"
  , "@ADD = λa. λb. λs. λz. !S&B=s; (a S₀ (b S₁ z))"
  , "@MUL = λa. λb. λs. λz. (a (b s) z)"
  , "@EXP = λa. λb. (b a)"
  , "@C1  = λs. λx. (s x)"
  , "@K1  = λs. λx. (s x)"
  , "@C2  = λs. !S0&C=s; λx0.(S0₀ (S0₁ x0))"
  , "@K2  = λs. !S0&K=s; λx0.(S0₀ (S0₁ x0))"
  , "@C4  = λs. !S0&C=s; !S1&C=λx0.(S0₀ (S0₁ x0)); λx1.(S1₀ (S1₁ x1))"
  , "@K4  = λs. !S0&K=s; !S1&K=λx0.(S0₀ (S0₁ x0)); !S2&K=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@C8  = λs. !S0&C=s; !S1&C=λx0.(S0₀ (S0₁ x0)); !S2&C=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@K8  = λs. !S0&K=s; !S1&K=λx0.(S0₀ (S0₁ x0)); !S2&K=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@id  = λa.a"
  , "@not = λ{#Z: #S{#Z{}}; λp. #Z{}}"
  , "@dbl = λ{#Z: #Z{}; λp. #S{#S{(@dbl p)}}}"
  , "@and = λ{#Z: λ{#Z: #Z{}; λp. #Z{}}; λp. λ{#Z: #Z{}; λq. #S{#Z{}}}}"
  , "@add = λ{#Z: λb.b; λa. λb. #S{(@add a b)}}"
  , "@sum = λ{#Z: #Z{}; λp. !P&S=p; #S{(@add P₀ (@sum P₁))}}"
  , "@foo = &L{λx.x,λ{#Z: #Z{}; λp. p}}"
  , "@gen = !F&A=@gen; &A{λx.!X&B=x;&B{X₀,#S{X₁}},λ{#Z:&C{#Z{},#S{#Z{}}};λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;#S{&E{(H₀ Q₀),#S{(H₁ Q₁)}}} }}}"
  , "@prd = λ{#Z: #Z{}; λp. p}"
  ]

tests :: [(String,String)]
tests =
  [ ("#Z{}", "#Z{}")
  , ("(@not #Z{})", "#S{#Z{}}")
  , ("(@not #S{#Z{}})", "#Z{}")
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and #Z{} #Z{})", "#Z{}")
  , ("(@and &L{#S{#Z{}},#Z{}} #S{#Z{}})", "&L{#S{#Z{}},#Z{}}")
  , ("(@and #S{#Z{}} &L{#Z{},#S{#Z{}}})", "&L{#Z{},#S{#Z{}}}")
  , ("(@sum #S{#S{#S{#Z{}}}})", "#S{#S{#S{#S{#S{#S{#Z{}}}}}}}")
  , ("(@foo #Z{})", "&L{#Z{},#Z{}}")
  , ("(@foo #S{#S{#S{#Z{}}}})", "&L{#S{#S{#S{#Z{}}}},#S{#S{#Z{}}}}")
  , ("#S{&L{#Z{},#S{#Z{}}}}", "&L{#S{#Z{}},#S{#S{#Z{}}}}")
  , ("(λx.x #A{})", "#A{}")
  , ("(λ{#A:λx.x; λx.x} #A{#B{}})", "#B{}")
  , ("(λ{#A:λx.x; λx.x} #C{#B{}})", "#B{}")
  , ("(λ{#A:λx.x; λx.#F{x}} #A{#B{}})", "#B{}")
  , ("(λ{#A:λx.x; λx.#F{x}} #C{#B{}})", "#F{#B{}}")
  , ("(λ{#A:λx.λy.y; λx.x} #A{#B{} #C{}})", "#C{}")
  , ("(@NOT @T)", "λa.λb.b")
  , ("(@NOT (@NOT @T))", "λa.λb.a")
  , ("(@C2 @NOT @T)", "λa.λb.a")
  , ("(@ADD @C2 @C1)", "λa.λb.(a (a (a b)))")
  , ("(@ADD @C1 @C4 @NOT @T)", "λa.λb.b")
  , ("(@MUL @C4 @C2)", "λa.λb.(a (a (a (a (a (a (a (a b))))))))")
  , ("(@EXP @C4 @K2)", "λa.λb.(a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))))")
  , ("(@EXP @C8 @K8 @NOT @T)", "λa.λb.a")
  ]

test :: IO ()
test = forM_ tests $ \ (src, exp) -> do
  !env <- new_env $ read_book book
  !det <- collapse env $ read_term src
  !det <- show <$> snf env 1 det
  !itr <- readIORef (env_inters env)
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " → " ++ det ++ " | #" ++ show itr
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det

-- Main
-- ====

run :: String -> String -> IO ()
run book_src term_src = do
  !env <- new_env $ read_book book_src
  !ini <- getCPUTime
  !val <- alloc env $ read_term term_src
  !val <- collapse env val
  !val <- snf env 1 val
  !end <- getCPUTime
  !itr <- readIORef (env_inters env)
  !dt  <- return $ fromIntegral (end - ini) / (10^12)
  !ips <- return $ fromIntegral itr / dt
  putStrLn $ show val
  putStrLn $ "- Itrs: " ++ show itr ++ " interactions"
  printf "- Time: %.3f seconds\n" (dt :: Double)
  printf "- Perf: %.2f M interactions/s\n" (ips / 1000000 :: Double)

main :: IO ()
main = test
