{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

module Main where

import Control.Monad (when, forM_)
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
  | Era
  | Sup !Lab !Term !Term
  | Dup !Name !Lab !Term !Term
  | Set
  | All !Term !Term
  | Lam !Name !Term
  | App !Term !Term
  | Nat
  | Zer
  | Suc !Term
  | Ref !Name
  | Nam !String
  | Dry !Term !Term
  deriving (Eq)

-- Funcs
-- -----
-- (note: constructors shouldn't be prefixed with "F")

data Func
  = Abs !Name !Func
  | Swi !Func !Func
  | Frk !Lab !Func !Func
  | Del
  | Ret !Term
  deriving (Eq, Show)

data Kind
  = VAR
  | DP0
  | DP1
  deriving (Enum)

data Book = Book (M.Map Name Func)

type Path = [(Lab, Int)]
type Subs = IM.IntMap Term

data Env = Env
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_sub_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

data Spine = Spine !Int !([Term] -> Term)

instance Show Spine where
  show sp = show (spine_term sp)

data Frame
  = FApp !Term
  | FDp0 !Name !Lab
  | FDp1 !Name !Lab
  deriving (Show)

type Stack = [Frame]

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name k
  show (Dp0 k)       = int_to_name k ++ "₀"
  show (Dp1 k)       = int_to_name k ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show Set           = "*"
  show (All a b)     = "∀" ++ show a ++ "." ++ show b
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f [x]
  show Nat           = "ℕ"
  show Zer           = "0"
  show (Suc p)       = show_add 1 p
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = (if debug then "." else "") ++ k
  show (Dry f x)     = (if debug then "." else "") ++ show_app f [x]

show_add :: Int -> Term -> String
show_add n (Suc p) = show_add (n + 1) p
show_add n Zer     = show n
show_add n term    = show n ++ "+" ++ show term

show_app :: Term -> [Term] -> String
show_app (Dry f x) args = show_app f (x : args)
show_app (App f x) args = show_app f (x : args)
show_app f         args = "(" ++ unwords (map show (f : args)) ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show_func ct | (k, ct) <- M.toList m ]

show_func :: Func -> String
show_func (Abs k f)   = "Λ" ++ int_to_name k ++ "." ++ show_func f
show_func (Swi z s)   = "Λ{0:" ++ show_func z ++ ";1+:" ++ show_func s ++ "}"
show_func (Frk k a b) = "&" ++ int_to_name k ++ "{" ++ show_func a ++ "," ++ show_func b ++ "}"
show_func Del         = "&{}"
show_func (Ret t)     = show t

-- Name Encoding/Decoding
-- ======================

alphabet :: String
alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

alphabet_first :: String
alphabet_first = filter (`notElem` "_0123456789") alphabet

name_to_int :: String -> Int
name_to_int = foldl' (\acc c -> (acc `shiftL` 6) + idx c) 0 where
  idx c = maybe (error "bad name char") id (elemIndex c alphabet)

int_to_name :: Int -> String
int_to_name 0 = "_"
int_to_name n = go n [] where
  go 0 acc = acc
  go m acc = let (q, r) = m `divMod` 64 in go q (alphabet !! r : acc)

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

parse_number :: ReadP Int
parse_number = read <$> munch1 isDigit

parse_nam :: ReadP String
parse_nam = lexeme $ do
  h <- satisfy (`elem` alphabet_first)
  t <- munch (`elem` alphabet)
  return (h : t)

parse_term :: ReadP Term
parse_term = parse_term_base

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam
  , parse_dup
  , parse_app
  , parse_era
  , parse_sup
  , parse_set
  , parse_all
  , parse_nat
  , parse_add
  , parse_num
  , parse_ref
  , parse_var
  ]

parse_app :: ReadP Term
parse_app = between (lexeme (char '(')) (lexeme (char ')')) $ do
  ts <- many1 parse_term
  let (f:args) = ts
  return (foldl' App f args)

parse_lam :: ReadP Term
parse_lam = do
  lexeme (choice [char 'λ', char '\\'])
  k <- parse_nam
  lexeme (char '.')
  body <- parse_term
  return (Lam (name_to_int k) body)

parse_dup :: ReadP Term
parse_dup = do
  lexeme (char '!')
  k <- parse_nam
  lexeme (char '&')
  l <- parse_nam
  lexeme (char '=')
  v <- parse_term
  optional (lexeme (char ';'))
  t <- parse_term
  return (Dup (name_to_int k) (name_to_int l) v t)

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_term
    optional (lexeme (char ','))
    b <- parse_term
    return (Sup (name_to_int l) a b)

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_set :: ReadP Term
parse_set = lexeme (char '*') >> return Set

parse_all :: ReadP Term
parse_all = do
  lexeme (char '∀')
  a <- parse_term_base
  lexeme (char '.')
  b <- parse_term
  return (All a b)

parse_nat :: ReadP Term
parse_nat = lexeme (char 'ℕ') >> return Nat

parse_ref :: ReadP Term
parse_ref = do
  lexeme (char '@')
  k <- parse_nam
  return (Ref (name_to_int k))

parse_add :: ReadP Term
parse_add = do
  value <- parse_number
  skipSpaces
  _ <- char '+'
  term <- parse_term_base
  return (iterate Suc term !! value)

parse_num :: ReadP Term
parse_num = do
  value <- parse_number
  return (iterate Suc Zer !! value)

parse_var :: ReadP Term
parse_var = do
  k <- parse_nam
  let kid = name_to_int k
  choice
    [ string "₀" >> return (Dp0 kid)
    , string "₁" >> return (Dp1 kid)
    , return (Var kid)
    ]

-- Func Parsing
-- ------------

parse_func :: ReadP Func
parse_func = lexeme $ choice
  [ parse_abs
  , parse_swi
  , parse_del
  , parse_frk
  , Ret <$> parse_term
  ]

parse_abs :: ReadP Func
parse_abs = do
  lexeme (char 'Λ')
  k <- parse_nam
  lexeme (char '.')
  body <- parse_func
  return (Abs (name_to_int k) body)

parse_swi :: ReadP Func
parse_swi = do
  lexeme (char 'Λ')
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "0:")
    z <- parse_func
    optional (lexeme (char ';'))
    lexeme (string "1+:")
    s <- parse_func
    return (Swi z s)

parse_del :: ReadP Func
parse_del = lexeme (string "&{}") >> return Del

parse_frk :: ReadP Func
parse_frk = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_func
    optional (lexeme (char ','))
    b <- parse_func
    return (Frk (name_to_int l) a b)

parse_book_entry :: ReadP (Name, Func)
parse_book_entry = do
  lexeme (char '@')
  k <- parse_nam
  lexeme (char '=')
  f <- parse_func
  return (name_to_int k, f)

parse_book :: ReadP Book
parse_book = do
  skipSpaces
  funcs <- many parse_book_entry
  skipSpaces
  eof
  return $ Book (M.fromList funcs)

read_term :: String -> Term
read_term s = case readP_to_S (parse_term <* skipSpaces <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse-term"

read_book :: String -> Book
read_book s = case readP_to_S parse_book s of
  [(b, "")] -> b
  _         -> error "bad-parse-book"

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
    Nothing -> return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = taker (env_dup_map e) k

take_sub :: Kind -> Env -> Name -> IO (Maybe Term)
take_sub ki e k = taker (env_sub_map e) (k `shiftL` 2 + fromEnum ki)

subst :: Kind -> Env -> Name -> Term -> IO ()
subst ki e k v =
  modifyIORef' (env_sub_map e) (IM.insert (k `shiftL` 2 + fromEnum ki) v)

duply :: Env -> Name -> Lab -> Term -> IO ()
duply e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  duply e k l v
  return (Dp0 k, Dp1 k)

clones :: Env -> Lab -> [Term] -> IO ([Term],[Term])
clones _ _ []       = return ([],[])
clones e l (x : xs) = do
  (x0  , x1 ) <- clone  e l x
  (xs0 , xs1) <- clones e l xs
  return (x0 : xs0 , x1 : xs1)

-- Cloning for Ref Logic
-- ---------------------

clone_ref_stack :: Env -> Lab -> Stack -> IO (Stack, Stack)
clone_ref_stack _ _ [] = return ([], [])
clone_ref_stack e l (frame : s) = do
  (f0, f1) <- case frame of
    FApp x -> do
      (x0, x1) <- clone e l x
      return (FApp x0, FApp x1)
    FDp0 k l' -> do
      (k0, k1) <- clone_ref_stack_dup e k l
      return (FDp0 k0 l', FDp0 k1 l')
    FDp1 k l' -> do
      (k0, k1) <- clone_ref_stack_dup e k l
      return (FDp1 k0 l', FDp1 k1 l')
  (s0, s1) <- clone_ref_stack e l s
  return (f0 : s0, f1 : s1)

clone_ref_stack_dup :: Env -> Name -> Lab -> IO (Name, Name)
clone_ref_stack_dup e k l = do
  k0 <- fresh e
  k1 <- fresh e
  subst DP0 e k (Sup l (Dp0 k0) (Dp0 k1))
  subst DP1 e k (Sup l (Dp1 k0) (Dp1 k1))
  return (k0, k1)

clone_ref_subst :: Env -> Lab -> Subs -> IO (Subs, Subs)
clone_ref_subst e l m = go (IM.toList m) IM.empty IM.empty where
  go []            m0 m1 = return (m0, m1)
  go ((k,v):rest)  m0 m1 = do
    (v0, v1) <- clone e l v
    go rest (IM.insert k v0 m0) (IM.insert k v1 m1)

-- Spine
-- =====

-- Only expose spine_new, spine_app and spine_ctr for extension.
-- Other helpers are for completion / inspection.

spine_new :: Name -> Spine
spine_new k = Spine 0 (\_ -> Ref k)

spine_app :: Spine -> Term -> Spine
spine_app (Spine n f) x = Spine n (\hs -> App (f hs) x)

spine_ctr :: Spine -> Spine
spine_ctr (Spine n f) = Spine (n + 1) (\(h:hs) -> App (f hs) (Suc h))

spine_term :: Spine -> Term
spine_term (Spine n f) = f (replicate n (Nam "_"))

-- Kind / Dir utilities
-- ====================

kind_term :: Kind -> Name -> Term
kind_term VAR k = Var k
kind_term DP0 k = Dp0 k
kind_term DP1 k = Dp1 k

dp_term :: Int -> Name -> Term
dp_term 0 k = Dp0 k
dp_term _ k = Dp1 k

-- WNF: Weak Normal Form
-- =====================

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

-- WNF: Enter
-- ----------

wnf_enter :: Env -> Stack -> Term -> IO Term

wnf_enter e s (Var k) = do
  when debug $ putStrLn $ ">> wnf_enter_var        : " ++ show (Var k)
  wnf_sub VAR e s k

wnf_enter e s (Dp0 k) = do
  when debug $ putStrLn $ ">> wnf_enter_dp0        : " ++ show (Dp0 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub DP0 e s k

wnf_enter e s (Dp1 k) = do
  when debug $ putStrLn $ ">> wnf_enter_dp1        : " ++ show (Dp1 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub DP1 e s k

wnf_enter e s (App f x) = do
  when debug $ putStrLn $ ">> wnf_enter_app        : " ++ show (App f x)
  wnf_enter e (FApp x : s) f

wnf_enter e s (Dup k l v t) = do
  when debug $ putStrLn $ ">> wnf_enter_dup        : " ++ show (Dup k l v t)
  duply e k l v
  wnf_enter e s t

wnf_enter e s (Ref k) = do
  when debug $ putStrLn $ ">> wnf_enter_ref        : " ++ show (Ref k)
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> wnf_ref_apply e (spine_new k) f s IM.empty []
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

wnf_enter e s f = do
  when debug $ putStrLn $ ">> wnf_enter            : " ++ show f
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind _ []    v = return v
wnf_unwind e (fr:s) v = do
  when debug $ putStrLn $ ">> wnf_unwind           : " ++ show v
  case fr of
    FApp x ->
      case v of
        Era          -> wnf_app_era e s x
        Sup fl fa fb -> wnf_app_sup e s fl fa fb x
        Set          -> wnf_app_set e s x
        All va vb    -> wnf_app_all e s va vb x
        Lam fk ff    -> wnf_app_lam e s fk ff x
        Nat          -> wnf_app_nat e s x
        Zer          -> wnf_app_zer e s x
        Suc vp       -> wnf_app_suc e s vp x
        Nam fk       -> wnf_app_nam e s fk x
        Dry ff fx    -> wnf_app_dry e s ff fx x
        f'           -> wnf_unwind e s (App f' x)
    FDp0 k l ->
      case v of
        Era          -> wnf_dpn_era 0 e s k l
        Sup vl va vb -> wnf_dpn_sup 0 e s k l vl va vb
        Set          -> wnf_dpn_set 0 e s k l
        All va vb    -> wnf_dpn_all 0 e s k l va vb
        Lam vk vf    -> wnf_dpn_lam 0 e s k l vk vf
        Nat          -> wnf_dpn_nat 0 e s k l
        Zer          -> wnf_dpn_zer 0 e s k l
        Suc vp       -> wnf_dpn_suc 0 e s k l vp
        Nam vk       -> wnf_dpn_nam 0 e s k l vk
        Dry vf vx    -> wnf_dpn_dry 0 e s k l vf vx
        val          -> wnf_unwind e s (Dup k l val (Dp0 k))
    FDp1 k l ->
      case v of
        Era          -> wnf_dpn_era 1 e s k l
        Sup vl va vb -> wnf_dpn_sup 1 e s k l vl va vb
        Set          -> wnf_dpn_set 1 e s k l
        All va vb    -> wnf_dpn_all 1 e s k l va vb
        Lam vk vf    -> wnf_dpn_lam 1 e s k l vk vf
        Nat          -> wnf_dpn_nat 1 e s k l
        Zer          -> wnf_dpn_zer 1 e s k l
        Suc vp       -> wnf_dpn_suc 1 e s k l vp
        Nam vk       -> wnf_dpn_nam 1 e s k l vk
        Dry vf vx    -> wnf_dpn_dry 1 e s k l vf vx
        val          -> wnf_unwind e s (Dup k l val (Dp1 k))

-- WNF: Interactions
-- -----------------

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  when debug $ putStrLn $ "## wnf_sub              : " ++ int_to_name k
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s (kind_term ki k)

wnf_app_era :: Env -> Stack -> Term -> IO Term
wnf_app_era e s v = do
  when debug $ putStrLn $ "## wnf_app_era          : " ++ show (App Era v)
  inc_inters e
  wnf e s Era

wnf_app_set :: Env -> Stack -> Term -> IO Term
wnf_app_set e _s v = do
  when debug $ putStrLn $ "## wnf_app_set          : " ++ show (App Set v)
  error "app-set"

wnf_app_all :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_all e _s va vb v = do
  when debug $ putStrLn $ "## wnf_app_all          : " ++ show (App (All va vb) v)
  error "app-all"

wnf_app_nat :: Env -> Stack -> Term -> IO Term
wnf_app_nat e _s v = do
  when debug $ putStrLn $ "## wnf_app_nat          : " ++ show (App Nat v)
  error "app-nat"

wnf_app_zer :: Env -> Stack -> Term -> IO Term
wnf_app_zer e _s v = do
  when debug $ putStrLn $ "## wnf_app_zer          : " ++ show (App Zer v)
  error "app-zer"

wnf_app_suc :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_suc e _s vp v = do
  when debug $ putStrLn $ "## wnf_app_suc          : " ++ show (App (Suc vp) v)
  error "app-suc"

wnf_app_nam :: Env -> Stack -> String -> Term -> IO Term
wnf_app_nam e s fk v = do
  when debug $ putStrLn $ "## wnf_app_nam          : " ++ show (App (Nam fk) v)
  wnf e s (Dry (Nam fk) v)

wnf_app_dry :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_dry e s ff fx v = do
  when debug $ putStrLn $ "## wnf_app_dry          : " ++ show (App (Dry ff fx) v)
  wnf e s (Dry (Dry ff fx) v)

wnf_app_lam :: Env -> Stack -> Name -> Term -> Term -> IO Term
wnf_app_lam e s fx ff v = do
  when debug $ putStrLn $ "## wnf_app_lam          : " ++ show (App (Lam fx ff) v)
  inc_inters e
  subst VAR e fx v
  wnf e s ff

wnf_app_sup :: Env -> Stack -> Lab -> Term -> Term -> Term -> IO Term
wnf_app_sup e s fL fa fb v = do
  when debug $ putStrLn $ "## wnf_app_sup          : " ++ show (App (Sup fL fa fb) v)
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

wnf_dpn_era :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnf_dpn_era d e s k _ = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_era          : " ++ show (Dup k (name_to_int "_") Era t)
  inc_inters e
  subst DP0 e k Era
  subst DP1 e k Era
  wnf e s t

wnf_dpn_sup :: Int -> Env -> Stack -> Name -> Lab -> Lab -> Term -> Term -> IO Term
wnf_dpn_sup d e s k l vl va vb
  | l == vl = do
      let t = dp_term d k
      when debug $ putStrLn $ "## wnf_dpn_sup_same     : " ++ show (Dup k l (Sup vl va vb) t)
      inc_inters e
      subst DP0 e k va
      subst DP1 e k vb
      wnf e s t
  | otherwise = do
      let t = dp_term d k
      when debug $ putStrLn $ "## wnf_dpn_sup_diff     : " ++ show (Dup k l (Sup vl va vb) t)
      inc_inters e
      (a0,a1) <- clone e l va
      (b0,b1) <- clone e l vb
      subst DP0 e k (Sup vl a0 b0)
      subst DP1 e k (Sup vl a1 b1)
      wnf e s t

wnf_dpn_set :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnf_dpn_set d e s k _ = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_set          : " ++ show (Dup k (name_to_int "_") Set t)
  inc_inters e
  subst DP0 e k Set
  subst DP1 e k Set
  wnf e s t

wnf_dpn_all :: Int -> Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnf_dpn_all d e s k l va vb = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_all          : " ++ show (Dup k l (All va vb) t)
  inc_inters e
  (a0,a1) <- clone e l va
  (b0,b1) <- clone e l vb
  subst DP0 e k (All a0 b0)
  subst DP1 e k (All a1 b1)
  wnf e s t

wnf_dpn_lam :: Int -> Env -> Stack -> Name -> Lab -> Name -> Term -> IO Term
wnf_dpn_lam d e s k l vk vf = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_lam          : " ++ show (Dup k l (Lam vk vf) t)
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst DP0 e k (Lam x0 g0)
  subst DP1 e k (Lam x1 g1)
  subst VAR e vk (Sup l (Var x0) (Var x1))
  wnf e s t

wnf_dpn_nat :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnf_dpn_nat d e s k _ = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_nat          : " ++ show (Dup k (name_to_int "_") Nat t)
  inc_inters e
  subst DP0 e k Nat
  subst DP1 e k Nat
  wnf e s t

wnf_dpn_zer :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnf_dpn_zer d e s k _ = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_zer          : " ++ show (Dup k (name_to_int "_") Zer t)
  inc_inters e
  subst DP0 e k Zer
  subst DP1 e k Zer
  wnf e s t

wnf_dpn_suc :: Int -> Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_suc d e s k l p = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_suc          : " ++ show (Dup k l (Suc p) t)
  inc_inters e
  (n0,n1) <- clone e l p
  subst DP0 e k (Suc n0)
  subst DP1 e k (Suc n1)
  wnf e s t

wnf_dpn_nam :: Int -> Env -> Stack -> Name -> Lab -> String -> IO Term
wnf_dpn_nam d e s k _ n = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_nam          : " ++ show (Dup k (name_to_int "_") (Nam n) t)
  inc_inters e
  subst DP0 e k (Nam n)
  subst DP1 e k (Nam n)
  wnf e s t

wnf_dpn_dry :: Int -> Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnf_dpn_dry d e s k l vf vx = do
  let t = dp_term d k
  when debug $ putStrLn $ "## wnf_dpn_dry          : " ++ show (Dup k l (Dry vf vx) t)
  inc_inters e
  (f0,f1) <- clone e l vf
  (x0,x1) <- clone e l vx
  subst DP0 e k (Dry f0 x0)
  subst DP1 e k (Dry f1 x1)
  wnf e s t

-- WNF: Ref Logic
-- --------------

wnf_ref_apply :: Env -> Spine -> Func -> Stack -> Subs -> Path -> IO Term
wnf_ref_apply e sp func s m p = do
  when debug $ putStrLn $ "## wnf_ref_apply        : " ++ show (spine_term sp) ++ " " ++ show func
  case s of
    FDp0 k l : s' -> wnf_ref_dp0 e sp func s' m p k l
    FDp1 k l : s' -> wnf_ref_dp1 e sp func s' m p k l
    _ -> case func of
      Abs k g   -> wnf_ref_fabs e sp k g s m p
      Swi z sc  -> wnf_ref_fswi e sp z sc s m p
      Frk k a b -> wnf_ref_ffrk e sp k a b s m p
      Del       -> wnf_ref_fdel e sp s m p
      Ret t     -> wnf_ref_fret e sp t s m p

wnf_ref_dp0 :: Env -> Spine -> Func -> Stack -> Subs -> Path -> Name -> Lab -> IO Term
wnf_ref_dp0 e sp func s m p _k l =
  wnf_ref_apply e sp func s m (p ++ [(l, 0)])

wnf_ref_dp1 :: Env -> Spine -> Func -> Stack -> Subs -> Path -> Name -> Lab -> IO Term
wnf_ref_dp1 e sp func s m p _k l =
  wnf_ref_apply e sp func s m (p ++ [(l, 1)])

wnf_ref_fabs :: Env -> Spine -> Name -> Func -> Stack -> Subs -> Path -> IO Term
wnf_ref_fabs e sp k g s m p =
  case s of
    FApp a : s' -> do
      inc_inters e
      let a' = wnf_ref_bind a p
      let m' = IM.insert k a' m
      let sp' = spine_app sp (Var k)
      wnf_ref_apply e sp' g s' m' p
    _ -> wnf_ref_stuck e sp s m p

wnf_ref_fswi :: Env -> Spine -> Func -> Func -> Stack -> Subs -> Path -> IO Term
wnf_ref_fswi e sp z sc s m p =
  case s of
    FApp t : s' -> do
      t_val <- wnf e [] t
      case t_val of
        Zer -> do
          inc_inters e
          let sp' = spine_app sp Zer
          wnf_ref_apply e sp' z s' m p
        Suc a -> do
          inc_inters e
          let sp' = spine_ctr sp
          wnf_ref_apply e sp' sc (FApp a : s') m p
        Sup l a b -> do
          inc_inters e
          (s0, s1) <- clone_ref_stack e l s'
          (m0, m1) <- clone_ref_subst e l m
          r0       <- wnf_ref_apply e sp (Swi z sc) (FApp a : s0) m0 (p ++ [(l, 0)])
          r1       <- wnf_ref_apply e sp (Swi z sc) (FApp b : s1) m1 (p ++ [(l, 1)])
          return (Sup l r0 r1)
        Era -> do
          return Era
        _ -> do
          wnf_ref_stuck e sp (FApp t_val : s') m p
    _ -> wnf_ref_stuck e sp s m p

wnf_ref_ffrk :: Env -> Spine -> Lab -> Func -> Func -> Stack -> Subs -> Path -> IO Term
wnf_ref_ffrk e sp k a b s m p =
  case lookup_path k p of
    Just 0 -> do
      let p' = remove_path k p
      wnf_ref_apply e sp a s m p'
    Just 1 -> do
      let p' = remove_path k p
      wnf_ref_apply e sp b s m p'
    Nothing -> do
      (s0, s1) <- clone_ref_stack e k s
      (m0, m1) <- clone_ref_subst e k m
      r0 <- wnf_ref_apply e sp a s0 m0 p
      r1 <- wnf_ref_apply e sp b s1 m1 p
      return (Sup k r0 r1)

wnf_ref_fdel :: Env -> Spine -> Stack -> Subs -> Path -> IO Term
wnf_ref_fdel _e _sp _s _m _p = return Era

wnf_ref_fret :: Env -> Spine -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_fret e _sp t s m p = do
  t <- alloc e m t
  t <- wnf_unwind e s t
  wnf_ref_wrap e t p

lookup_path :: Lab -> Path -> Maybe Int
lookup_path k = go Nothing where
  go acc [] = acc
  go acc ((l,d):ps)
    | k == l    = go (Just d) ps
    | otherwise = go acc ps

remove_path :: Lab -> Path -> Path
remove_path k p = snd (go p) where
  go [] = (False, [])
  go ((l,d):ps) =
    let (removed, ps') = go ps in
    if removed
      then (True, (l,d) : ps')
      else if k == l
            then (True, ps')
            else (False, (l,d) : ps')

wnf_ref_stuck :: Env -> Spine -> Stack -> Subs -> Path -> IO Term
wnf_ref_stuck e sp s m p = do
  t <- alloc e m (spine_term sp)
  t <- wnf_unwind e s t
  wnf_ref_wrap e t p

-- Alloc / Bind / Wrap
-- -------------------

alloc :: Env -> Subs -> Term -> IO Term
alloc e subs term = go subs IM.empty term where
  go :: Subs -> IM.IntMap Name -> Term -> IO Term
  go s r (Var k) =
    case IM.lookup k s of
      Just v  -> return v
      Nothing -> return (Var (IM.findWithDefault k k r))
  go _ r (Dp0 k)       = return (Dp0 (IM.findWithDefault k k r))
  go _ r (Dp1 k)       = return (Dp1 (IM.findWithDefault k k r))
  go _ _ Era           = return Era
  go s r (Sup l a b)   = do
    a' <- go s r a
    b' <- go s r b
    return (Sup l a' b')
  go s r (Dup k l v t) = do
    k' <- fresh e
    v' <- go s r v
    t' <- go s (IM.insert k k' r) t
    return (Dup k' l v' t')
  go _ _ Set           = return Set
  go s r (All a b)     = All <$> go s r a <*> go s r b
  go s r (Lam k f)     = do
    k' <- fresh e
    f' <- go s (IM.insert k k' r) f
    return (Lam k' f')
  go s r (App f x)     = App <$> go s r f <*> go s r x
  go _ _ Nat           = return Nat
  go _ _ Zer           = return Zer
  go s r (Suc n)       = Suc <$> go s r n
  go _ _ (Ref k)       = return (Ref k)
  go _ _ (Nam x)       = return (Nam x)
  go s r (Dry f x)     = Dry <$> go s r f <*> go s r x

wnf_ref_bind :: Term -> Path -> Term
wnf_ref_bind x []           = x
wnf_ref_bind x ((l,0):p)    = Sup l (wnf_ref_bind x p) Era
wnf_ref_bind x ((l,1):p)    = Sup l Era (wnf_ref_bind x p)

wnf_ref_wrap :: Env -> Term -> Path -> IO Term
wnf_ref_wrap _e t []          = return t
wnf_ref_wrap e  t ((l,d):p) = do
  k <- fresh e
  t <- wnf_ref_wrap e t p
  case d of
    0 -> return (Dup k l t (Dp0 k))
    1 -> return (Dup k l t (Dp1 k))
    _ -> error "invalid direction in path"

-- Normalization
-- =============

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x' <- wnf e [] x
  case x' of
    Var k -> return $ Var k
    Dp0 k -> return $ Dp0 k
    Dp1 k -> return $ Dp1 k
    Era -> return Era
    Sup l a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Sup l a' b'
    Dup k l v t -> do
      subst DP0 e k (Nam (int_to_name d ++ "₀"))
      subst DP1 e k (Nam (int_to_name d ++ "₁"))
      v' <- snf e d v
      t' <- snf e d t
      return $ Dup d l v' t'
    Set -> return Set
    All a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ All a' b'
    Lam k f -> do
      subst VAR e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'
    App f x1 -> do
      f' <- snf e d f
      x'' <- snf e d x1
      return $ App f' x''
    Nat -> return Nat
    Zer -> return Zer
    Suc p -> do
      p' <- snf e d p
      return $ Suc p'
    Ref k -> return $ Ref k
    Nam k -> return $ Nam k
    Dry f x1 -> do
      f' <- snf e d f
      x'' <- snf e d x1
      return $ Dry f' x''

-- Collapsing
-- ==========

col :: Env -> Term -> IO Term
col e x = do
  !x' <- wnf e [] x
  case x' of
    Era -> return Era
    Sup l a b -> do
      a' <- col e a
      b' <- col e b
      return $ Sup l a' b'
    Set -> return Set
    All a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- col e a
      b' <- col e b
      inj e (Lam aV (Lam bV (All (Var aV) (Var bV)))) [a',b']
    Lam k f -> do
      fV <- fresh e
      f' <- col e f
      inj e (Lam fV (Lam k (Var fV))) [f']
    App f x1 -> do
      fV <- fresh e
      xV <- fresh e
      f' <- col e f
      x' <- col e x1
      inj e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Nat -> return Nat
    Zer -> return Zer
    Suc p -> do
      pV <- fresh e
      p' <- col e p
      inj e (Lam pV (Suc (Var pV))) [p']
    Nam n -> return $ Nam n
    Dry f x1 -> do
      fV <- fresh e
      xV <- fresh e
      f' <- col e f
      x' <- col e x1
      inj e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    x'' -> return x''

inj :: Env -> Term -> [Term] -> IO Term
inj e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    Sup l a b -> do
      (f0  , f1 ) <- clone  e l f
      (xs0 , xs1) <- clones e l xs
      a' <- inj e f0 (a : xs0)
      b' <- inj e f1 (b : xs1)
      return $ Sup l a' b'
    x'' -> inj e (App f x'') xs
inj _ f [] = return f

-- Main
-- ====

f :: Int -> String
f n = "λf." ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00&A=f;"
  dup i = "!F" ++ pad i ++ "&A=λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));"
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

tests :: [(String,String)]
tests =
  [ ("0", "0")
  , ("(@not 0)", "1")
  , ("(@not 1+0)", "0")
  -- , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(@and 0 a)")
  , ("λx.(@and x 0)", "λa.(@and a 0)")
  -- , ("(@sum 1+1+1+0)", "6")
  -- , ("λx.(@sum 1+1+1+x)", "λa.3+(@add a 2+(@add a 1+(@add a (@sum a))))")
  , ("(@foo 0)", "&L{0,0}")
  , ("(@foo 1+1+1+0)", "&L{3,2}")
  , ("λx.(@dbl 1+1+x)", "λa.4+(@dbl a)")
  , ("("++f 2++" λX.(X λT0.λF0.F0 λT1.λF1.T1) λT2.λF2.T2)", "λa.λb.a")
  , ("1+&L{0,1}", "&L{1,2}")
  , ("1+&A{&B{0,1},&C{2,3}}", "&A{&B{1,2},&C{3,4}}")
  , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  , ("λa.λb.!A&L=a;!B&L=b;&L{λx.(x A₀ B₀),λx.(x A₁ B₁)}", "&L{λa.λb.λc.(c a b),λa.λb.λc.(c a b)}")
  , ("λt.(t &A{1,2} 3)", "&A{λa.(a 1 3),λa.(a 2 3)}")
  , ("λt.(t 1 &B{3,4})", "&B{λa.(a 1 3),λa.(a 1 4)}")
  , ("λt.(t &A{1,2} &A{3,4})", "&A{λa.(a 1 3),λa.(a 2 4)}")
  , ("λt.(t &A{1,2} &B{3,4})", "&A{&B{λa.(a 1 3),λa.(a 1 4)},&B{λa.(a 2 3),λa.(a 2 4)}}")
  -- , ("@gen", "&A{&B{λa.a,λa.1+a},&C{&D{λ{0:0;1+:λa.(@gen a)},&E{λ{0:0;1+:λa.1+(@gen a)},λ{0:0;1+:λa.2+(@gen a)}}},&D{λ{0:1;1+:λa.(@gen a)},&E{λ{0:1;1+:λa.1+(@gen a)},λ{0:1;1+:λa.2+(@gen a)}}}}}")
  -- , ("λx.(@gen 2+x)", "&A{&B{λa.2+a,λa.3+a},&D{λa.(@gen a),&E{λa.2+(@gen a),λa.4+(@gen a)}}}")
  -- , ("(@gen 2)", "&A{&B{2,3},&D{&C{0,1},&E{&C{2,3},&C{4,5}}}}")
  ]

book :: String
book = unlines
  [ ""
  , "@id  = Λa.a"
  , "@not = Λ{0:1+0;1+:Λp.0}"
  , "@dbl = Λ{0:0;1+:Λp.1+1+(@dbl p)}"
  , "@and = Λ{0:Λ{0:0;1+:Λp.0};1+:Λp.Λ{0:0;1+:Λp.1+0}}"
  , "@add = Λ{0:Λb.b;1+:Λa.Λb.1+(@add a b)}"
  , "@sum = Λ{0:0;1+:Λp.!P&S=p;1+(@add P₀ (@sum P₁))}"
  , "@foo = &L{Λx.x,Λ{0:0;1+:Λp.p}}"
  -- , "@gen = !F&A=@gen &A{Λx.!X&B=x;&B{X₀,1+X₁},Λ{0:&C{0,1};1+:Λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  ]

run :: String -> String -> IO ()
run book_src term_src = do
  !env <- new_env $ read_book book_src
  !ini <- getCPUTime
  !val <- alloc env IM.empty (read_term term_src)
  !val <- col env val
  !val <- snf env 1 val
  !end <- getCPUTime
  !itr <- readIORef (env_inters env)
  let dt  = fromIntegral (end - ini) / (10^12)
      ips = fromIntegral itr / dt
  putStrLn $ show val
  putStrLn $ "- Itrs: " ++ show itr ++ " interactions"
  printf "- Time: %.3f seconds\n" (dt :: Double)
  printf "- Perf: %.2f M interactions/s\n" (ips / 1000000 :: Double)

test :: IO ()
test = forM_ tests $ \ (src, expd) -> do
  env <- new_env $ read_book book
  det <- col env $ read_term src
  det <- show <$> snf env 1 det
  if det == expd then do
    putStrLn $ "[PASS] " ++ src ++ " -> " ++ det
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ expd
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = test
