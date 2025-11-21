{-# LANGUAGE BangPatterns, CPP #-}

import Control.Monad (forM_, when)
import Data.Bits (shiftL)
import Data.Char (isDigit)
import Data.IORef
import Data.List (foldl', elemIndex, intercalate)
import System.CPUTime
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
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
  | Cop !Int !Name
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
  | Alo ![Name] !Term
  deriving (Eq)

data Book = Book (M.Map Name Term)

data Env = Env
  { env_book  :: !Book
  , env_itrs  :: !(IORef Int)
  , env_fresh :: !(IORef Int)
  , env_subst :: !(IORef (IM.IntMap Term))
  , env_dups  :: !(IORef (IM.IntMap (Lab, Term)))
  }

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name k
  show (Cop s k)     = int_to_name k ++ (if s == 0 then "₀" else "₁")
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = k
  show (Dry f x)     = show_app f x
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f x
  show (Ctr k xs)    = "#" ++ int_to_name k ++ "{" ++ intercalate "," (map show xs) ++ "}"
  show (Mat k h m)   = "λ{#" ++ int_to_name k ++ ":" ++ show h ++ ";" ++ show m ++ "}"
  show (Alo s t)     = "@{" ++ intercalate "," (map int_to_name s) ++ "}" ++ show t

show_app :: Term -> Term -> String
show_app f x = case f of
  App _ _ -> init (show f) ++ "," ++ show x ++ ")"
  Dry _ _ -> init (show f) ++ "," ++ show x ++ ")"
  Lam _ _ -> "(" ++ show f ++ ")(" ++ show x ++ ")"
  _       -> show f ++ "(" ++ show x ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

show_dups  :: IM.IntMap (Lab, Term) -> String
show_dups  m = unlines [ "! " ++ int_to_name k ++ " &" ++ int_to_name l ++ " = " ++ show v | (k, (l, v)) <- IM.toList m ]

show_subst :: IM.IntMap Term -> String
show_subst m = unlines [ int_to_name (k `div` 4) ++ suffix (k `mod` 4) ++ " ← " ++ show v | (k, v) <- IM.toList m ]
  where suffix x = case x of { 0 -> "" ; 1 -> "₀" ; 2 -> "₁" ; _ -> "?" }

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
int_to_name n | n <  64 = [alphabet !! n]
              | n >= 64 = int_to_name (n `div` 64) ++ [alphabet !! (n `mod` 64)]

-- Parsing
-- =======

parse_lexeme :: ReadP a -> ReadP a
parse_lexeme p = skipSpaces *> p

parse_name :: ReadP String
parse_name = parse_lexeme $ do
  head <- satisfy (`elem` alphabet_first)
  tail <- munch (`elem` alphabet)
  return (head : tail)

parse_term :: ReadP Term
parse_term = do
  t <- parse_term_base
  parse_term_suff t

parse_term_suff :: Term -> ReadP Term
parse_term_suff t = loop <++ return t where
  loop = do
    parse_lexeme (char '(')
    args <- sepBy parse_term (parse_lexeme (char ','))
    parse_lexeme (char ')')
    parse_term_suff (foldl' App t args)

parse_term_base :: ReadP Term
parse_term_base = parse_lexeme $ choice
  [ parse_lam_or_swi
  , parse_dup
  , parse_sup
  , parse_era
  , parse_ctr
  , parse_ref
  , parse_nam
  , parse_par
  , parse_var
  ]

parse_par :: ReadP Term
parse_par = do
  parse_lexeme (char '(')
  t <- parse_term
  parse_lexeme (char ')')
  return t

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  parse_lexeme (char 'λ')
  choice
    [ parse_lam_brace
    , parse_lam_var
    ]

parse_lam_brace :: ReadP Term
parse_lam_brace = do
  parse_lexeme (char '{')
  t <- parse_mat
  parse_lexeme (char '}')
  return t

parse_lam_var :: ReadP Term
parse_lam_var = do
  k <- parse_name
  parse_lexeme (char '.')
  t <- parse_term
  return (Lam (name_to_int k) t)

parse_mat :: ReadP Term
parse_mat = do
  parse_lexeme (char '#')
  k <- parse_name
  parse_lexeme (char ':')
  h <- parse_term
  optional (parse_lexeme (char ';'))
  m <- parse_term
  return (Mat (name_to_int k) h m)

parse_dup :: ReadP Term
parse_dup = do
  parse_lexeme (char '!')
  k <- parse_name
  parse_lexeme (char '&')
  l <- parse_name
  parse_lexeme (char '=')
  v <- parse_term
  optional (parse_lexeme (char ';'))
  t <- parse_term
  return (Dup (name_to_int k) (name_to_int l) v t)

parse_sup :: ReadP Term
parse_sup = do
  parse_lexeme (char '&')
  l <- parse_name
  between (parse_lexeme (char '{')) (parse_lexeme (char '}')) $ do
    a <- parse_term
    optional (parse_lexeme (char ','))
    b <- parse_term
    return (Sup (name_to_int l) a b)

parse_era :: ReadP Term
parse_era = parse_lexeme (string "&{}") >> return Era

parse_ref :: ReadP Term
parse_ref = do
  parse_lexeme (char '@')
  k <- parse_name
  return (Ref (name_to_int k))

parse_var :: ReadP Term
parse_var = do
  k <- parse_name
  let kid = name_to_int k
  choice
    [ string "₀" >> return (Cop 0 kid)
    , string "₁" >> return (Cop 1 kid)
    , return (Var kid)
    ]

parse_ctr :: ReadP Term
parse_ctr = do
  parse_lexeme (char '#')
  k <- parse_name
  parse_lexeme (char '{')
  xs <- sepBy parse_term (parse_lexeme (char ','))
  parse_lexeme (char '}')
  return (Ctr (name_to_int k) xs)

parse_nam :: ReadP Term
parse_nam = do
  parse_lexeme (char '^')
  choice
    [ parse_nam_dry
    , parse_nam_var
    ]

parse_nam_dry :: ReadP Term
parse_nam_dry = do
  parse_lexeme (char '(')
  f <- parse_term
  parse_lexeme (char ',')
  x <- parse_term
  parse_lexeme (char ')')
  return (Dry f x)

parse_nam_var :: ReadP Term
parse_nam_var = do
  k <- parse_name
  return (Nam k)

parse_func :: ReadP (Name, Term)
parse_func = do
  parse_lexeme (char '@')
  k <- parse_name
  parse_lexeme (char '=')
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
  [(t, "")] -> bruijn t
  _         -> error "bad-parse"

read_book :: String -> Book
read_book s = case readP_to_S parse_book s of
  [(Book m, "")] -> Book (M.map bruijn m)
  _              -> error "bad-parse"

bruijn :: Term -> Term
bruijn t = go IM.empty 0 t where
  go :: IM.IntMap Int -> Int -> Term -> Term
  go env d t = case t of
    Var k       -> case IM.lookup k env of { Just l -> Var (d - 1 - l) ; Nothing -> Var k }
    Cop s k     -> case IM.lookup k env of { Just l -> Cop s (d - 1 - l) ; Nothing -> Cop s k }
    Ref k       -> Ref k
    Nam k       -> Nam k
    Dry f x     -> Dry (go env d f) (go env d x)
    Era         -> Era
    Sup l a b   -> Sup l (go env d a) (go env d b)
    Dup k l v b -> Dup k l (go env d v) (go (IM.insert k d env) (d + 1) b)
    Lam k f     -> Lam k (go (IM.insert k d env) (d + 1) f)
    App f x     -> App (go env d f) (go env d x)
    Ctr k xs    -> Ctr k (map (go env d) xs)
    Mat k h m   -> Mat k (go env d h) (go env d m)
    Alo s b     -> Alo s (go env d b)

-- Environment
-- ===========

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 1
  sub <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids sub dm

inc_itrs :: Env -> IO ()
inc_itrs e = do
  !n <- readIORef (env_itrs e)
  writeIORef (env_itrs e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (env_fresh e)
  writeIORef (env_fresh e) (n + 1)
  return ((n `shiftL` 6) + 63)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = atomicModifyIORef' (env_dups  e) $ \m -> (IM.delete k m, IM.lookup k m)

take_sub :: Env -> Name -> IO (Maybe Term)
take_sub e k = atomicModifyIORef' (env_subst e) $ \m -> (IM.delete k m, IM.lookup k m)

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dups  e) (IM.insert k (l, v))

subst :: Env -> Name -> Term -> IO ()
subst e k v = modifyIORef' (env_subst e) (IM.insert k v)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Cop 0 k , Cop 1 k)

clone_list :: Env -> Lab -> [Term] -> IO ([Term], [Term])
clone_list e l []     = return ([], [])
clone_list e l (h:t) = do
  (h0, h1) <- clone e l h
  (t0, t1) <- clone_list e l t
  return (h0:t0, h1:t1)

-- WNF: Weak Normal Form
-- =====================

type WnfApp = Env -> Term -> Term -> IO Term
type WnfDup = Int -> Env -> Name -> Lab -> Term -> IO Term

wnf :: Env -> Term -> IO Term
wnf e term = do
  when debug $ putStrLn $ "wnf: " ++ show term
  case term of
    Var k -> do
      wnf_var e k
    Cop s k -> do
      got <- take_dup e k
      case got of
        Just (l, v) -> do
          v <- wnf e v
          case v of
            Era   -> wnf_dup_era s e k l v
            Sup{} -> wnf_dup_sup s e k l v
            Lam{} -> wnf_dup_lam s e k l v
            Nam{} -> wnf_dup_nam s e k l v
            Dry{} -> wnf_dup_dry s e k l v
            Ctr{} -> wnf_dup_ctr s e k l v
            Mat{} -> wnf_dup_mat s e k l v
            _     -> return (Dup k l v (Cop s k))
        Nothing -> do
          wnf_cop s e k
    App f x -> do
      f <- wnf e f
      case f of
        Era   -> wnf_app_era e f x
        Sup{} -> wnf_app_sup e f x
        Lam{} -> wnf_app_lam e f x
        Nam{} -> wnf_app_nam e f x
        Dry{} -> wnf_app_dry e f x
        Mat k h m -> do
          x <- wnf e x
          case x of
            Era      -> wnf_app_mat_era e f x
            Sup{}    -> wnf_app_mat_sup e f x
            Ctr k' a -> wnf_app_mat_ctr e f k h m k' a
            _        -> return (App f x)
        _ -> return (App f x)
    Dup k l v t -> do
      make_dup e k l v
      wnf e t
    Ref k -> do
      wnf_ref e k
    Alo s t -> case t of
      Var k     -> wnf e $ Var (s !! k)
      Cop c k   -> wnf e $ Cop c (s !! k)
      Ref k     -> wnf e $ Ref k
      Nam k     -> wnf e $ Nam k
      Dry f x   -> wnf e $ Dry (Alo s f) (Alo s x)
      Era       -> wnf e $ Era
      Sup l a b -> wnf e $ Sup l (Alo s a) (Alo s b)
      Dup k l v t -> do
        x <- fresh e
        wnf e $ Dup x l (Alo s v) (Alo (x:s) t)
      Lam k f -> do
        x <- fresh e
        wnf e $ Lam x (Alo (x:s) f)
      App f x   -> wnf e $ App (Alo s f) (Alo s x)
      Ctr k xs  -> wnf e $ Ctr k (map (Alo s) xs)
      Mat k h m -> wnf e $ Mat k (Alo s h) (Alo s m)
      Alo s' t' -> error "Nested Alo"
    t -> do
      return t

-- WNF: Interactions
-- =================

wnf_var :: Env -> Name -> IO Term
wnf_var e k = do
  when debug $ putStrLn $ "wnf_var: " ++ show (Var k)
  mt <- take_sub e k
  case mt of
    Just t  -> wnf e t
    Nothing -> return $ Var k

wnf_cop :: Int -> Env -> Name -> IO Term
wnf_cop i e k = do
  when debug $ putStrLn $ "wnf_cop: " ++ show (Cop i k)
  mt <- take_sub e k
  case mt of
    Just t  -> wnf e t
    Nothing -> return $ Cop i k

wnf_dup_era :: WnfDup
wnf_dup_era i e k _ Era = do
  inc_itrs e
  subst e k Era
  wnf e Era

wnf_dup_sup :: WnfDup
wnf_dup_sup i e k l (Sup vl va vb)
  | l == vl = do
      inc_itrs e
      if i == 0 then do
        subst e k vb
        wnf e va
      else do
        subst e k va
        wnf e vb
  | otherwise = do
      inc_itrs e
      (va0, va1) <- clone e l va
      (vb0, vb1) <- clone e l vb
      if i == 0 then do
        subst e k (Sup vl va1 vb1)
        wnf e (Sup vl va0 vb0)
      else do
        subst e k (Sup vl va0 vb0)
        wnf e (Sup vl va1 vb1)

wnf_dup_lam :: WnfDup
wnf_dup_lam i e k l (Lam vk vf) = do
  inc_itrs e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst e vk (Sup l (Var x0) (Var x1))
  if i == 0 then do
    subst e k (Lam x1 g1)
    wnf e (Lam x0 g0)
  else do
    subst e k (Lam x0 g0)
    wnf e (Lam x1 g1)

wnf_dup_nam :: WnfDup
wnf_dup_nam i e k _ (Nam n) = do
  inc_itrs e
  subst e k (Nam n)
  wnf e (Nam n)

wnf_dup_dry :: WnfDup
wnf_dup_dry i e k l (Dry vf vx) = do
  inc_itrs e
  (vf0, vf1) <- clone e l vf
  (vx0, vx1) <- clone e l vx
  if i == 0 then do
    subst e k (Dry vf1 vx1)
    wnf e (Dry vf0 vx0)
  else do
    subst e k (Dry vf0 vx0)
    wnf e (Dry vf1 vx1)

wnf_dup_ctr :: WnfDup
wnf_dup_ctr i e k l (Ctr kn xs) = do
  inc_itrs e
  (xsA, xsB) <- clone_list e l xs
  if i == 0 then do
    subst e k (Ctr kn xsB)
    wnf e (Ctr kn xsA)
  else do
    subst e k (Ctr kn xsA)
    wnf e (Ctr kn xsB)

wnf_dup_mat :: WnfDup
wnf_dup_mat i e k l (Mat kn h m) = do
  inc_itrs e
  (hA, hB) <- clone e l h
  (mA, mB) <- clone e l m
  if i == 0 then do
    subst e k (Mat kn hB mB)
    wnf e (Mat kn hA mA)
  else do
    subst e k (Mat kn hA mA)
    wnf e (Mat kn hB mB)

wnf_app_era :: WnfApp
wnf_app_era e Era v = do
  inc_itrs e
  wnf e Era

wnf_app_nam :: WnfApp
wnf_app_nam e (Nam fk) v = wnf e (Dry (Nam fk) v)

wnf_app_dry :: WnfApp
wnf_app_dry e (Dry ff fx) v = wnf e (Dry (Dry ff fx) v)

wnf_app_lam :: WnfApp
wnf_app_lam e (Lam fx ff) v = do
  inc_itrs e
  subst e fx v
  wnf e ff

wnf_app_sup :: WnfApp
wnf_app_sup e (Sup fL fa fb) v = do
  inc_itrs e
  (x0,x1) <- clone e fL v
  wnf e (Sup fL (App fa x0) (App fb x1))

wnf_app_mat_era :: WnfApp
wnf_app_mat_era e f x = do
  inc_itrs e
  wnf e Era

wnf_app_mat_sup :: WnfApp
wnf_app_mat_sup e (Mat k h m) (Sup l x y) = do
  inc_itrs e
  (h0, h1) <- clone e l h
  (m0, m1) <- clone e l m
  wnf e (Sup l (App (Mat k h0 m0) x) (App (Mat k h1 m1) y))

wnf_app_mat_ctr :: Env -> Term -> Int -> Term -> Term -> Int -> [Term] -> IO Term
wnf_app_mat_ctr e f k h m k' xs = do
  inc_itrs e
  if k == k' then do
    wnf e (foldl' App h xs)
  else do
    wnf e (App m (Ctr k' xs))

wnf_ref :: Env -> Name -> IO Term
wnf_ref e k = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_itrs e
      wnf e (Alo [] f)
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

-- Normalization
-- =============

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x' <- wnf e x
  case x' of

    Var k -> do
      return $ Var k

    Cop s k -> do
      return $ Cop s k

    Era -> do
      return $ Era

    Sup l a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Sup l a' b'

    Dup k l v t -> do
      error "TODO"

    Lam k f -> do
      subst e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'

    App f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ App f' x'

    Ref k -> do
      return $ Ref k

    Nam k -> do
      return $ Nam k

    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'

    Ctr k xs -> do
      xs' <- mapM (snf e d) xs
      return $ Ctr k xs'

    Mat k h m -> do
      h' <- snf e d h
      m' <- snf e d m
      return $ Mat k h' m'

    Alo s t -> do
      error "Should be gone"

-- Collapsing
-- ==========

collapse :: Env -> Term -> IO Term
collapse e x = do
  !x <- wnf e x
  case x of

    Era -> do
      return Era

    (Sup l a b) -> do
      a' <- collapse e a
      b' <- collapse e b
      return $ Sup l a' b'

    (Lam k f) -> do
      fV <- fresh e
      f' <- collapse e f
      inject e (Lam fV (Lam k (Var fV))) [f']

    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f', x']

    Nam n -> do
      return $ Nam n

    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f', x']

    Ctr k xs -> do
      vs <- mapM (\_ -> fresh e) xs
      as <- mapM (collapse e) xs
      inject e (foldr Lam (Ctr k (map Var vs)) vs) as

    Mat k h m -> do
      hV <- fresh e
      mV <- fresh e
      h' <- collapse e h
      m' <- collapse e m
      inject e (Lam hV (Lam mV (Mat k (Var hV) (Var mV)))) [h', m']

    x -> do
      return $ x

inject :: Env -> Term -> [Term] -> IO Term
inject e f [] = return f
inject e f (h:t) = do
  !h <- wnf e h
  case h of
    Sup l a b -> do
      (f0,f1) <- clone e l f
      (t0,t1) <- clone_list e l t
      a' <- inject e f0 (a:t0)
      b' <- inject e f1 (b:t1)
      return $ Sup l a' b'
    _ -> do
      inject e (App f h) t

flatten :: Term -> [Term]
flatten term = bfs [term] [] where
  bfs []     acc = reverse acc
  bfs (t:ts) acc = case t of
    Sup _ a b -> bfs (ts ++ [a, b]) acc
    _         -> bfs ts (t : acc)
