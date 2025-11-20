--[./README.md]

{-# LANGUAGE BangPatterns, CPP #-}

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
  | Set
  | All !Term !Term
  | Lam !Name !Term
  | App !Term !Term
  | Sig !Term !Term
  | Tup !Term !Term
  | Get !Term
  | Emp
  | Efq
  | Uni
  | One
  | Use !Term
  | Bol
  | Fal
  | Tru
  | If !Term !Term
  | Nat
  | Zer
  | Suc !Term
  | Swi !Term !Term
  | Lst !Term
  | Nil
  | Con !Term !Term
  | Mat !Term !Term
  | And !Term !Term
  | Eql !Term !Term
  | Gua !Term !Term
  | Gen !Name !Term !Term !Term !Term
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
  show Set           = "*"
  show (All a b)     = "∀" ++ show a ++ "." ++ show b
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f [x]
  show (Sig a b)     = "Σ" ++ show a ++ "." ++ show b
  show (Tup a b)     = "(" ++ show a ++ "," ++ show b ++ ")"
  show (Get c)       = "λ{,:" ++ show c ++ "}"
  show Emp           = "⊥"
  show Efq           = "λ{}"
  show Uni           = "⊤"
  show One           = "()"
  show (Use u)       = "λ{():" ++ show u ++ "}"
  show Bol           = "𝔹"
  show Fal           = "#F"
  show Tru           = "#T"
  show (If f t)      = "λ{#F:" ++ show f ++ ";#T:" ++ show t ++ "}"
  show Nat           = "ℕ"
  show Zer           = "0"
  show (Suc p)       = show_add 1 p
  show (Swi z s)     = "λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (Lst t)       = show t ++ "[]"
  show Nil           = "[]"
  show (Con h t)     = show h ++ "<>" ++ show t
  show (Mat n c)     = "λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (And a b)     = show a ++ "&&" ++ show b
  show (Eql a b)     = show a ++ "==" ++ show b
  show (Gua f g)     = show f ++ "~>" ++ show g

show_add :: Int -> Term -> String
show_add n Zer     = show n
show_add n (Suc p) = show_add (n + 1) p
show_add n term    = show n ++ "+" ++ show term

show_app :: Term -> [Term] -> String
show_app (Dry f x) args = show_app f (x : args)
show_app (App f x) args = show_app f (x : args)
show_app f         args = "(" ++ unwords (map show (f : args)) ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

show_dup_map :: IM.IntMap (Lab, Term) -> String
show_dup_map m = unlines [ "! " ++ int_to_name k ++ " &" ++ int_to_name l ++ " = " ++ show v | (k, (l, v)) <- IM.toList m ]

show_sub_map :: IM.IntMap Term -> String
show_sub_map m = unlines [ int_to_name (k `div` 4) ++ suffix (k `mod` 4) ++ " ← " ++ show v | (k, v) <- IM.toList m ]
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

parse_term :: ReadP Term
parse_term = do
  t <- parse_term_base
  parse_term_suff t

parse_term_suff :: Term -> ReadP Term
parse_term_suff t = skipSpaces >> choice
  [ parse_op_and t
  , parse_op_eql t
  , parse_op_gua t
  , parse_op_lst t
  , parse_op_con t
  , return t
  ]

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam_or_swi
  , parse_dup
  , parse_par
  , parse_sup
  , parse_era
  , parse_set
  , parse_all
  , parse_sig
  , parse_nat
  , parse_add
  , parse_num
  , parse_ref
  , parse_emp
  , parse_uni
  , parse_bol
  , parse_ctr
  , parse_nil
  , parse_nam
  , parse_var
  ]

parse_op_and :: Term -> ReadP Term
parse_op_and t = do
  string "&&"
  t2 <- parse_term
  return (And t t2)

parse_op_eql :: Term -> ReadP Term
parse_op_eql t = do
  string "=="
  t2 <- parse_term
  return (Eql t t2)

parse_op_gua :: Term -> ReadP Term
parse_op_gua t = do
  string "~>"
  t2 <- parse_term
  return (Gua t t2)

parse_op_lst :: Term -> ReadP Term
parse_op_lst t = do
  string "[]"
  parse_term_suff (Lst t)

parse_op_con :: Term -> ReadP Term
parse_op_con t = do
  string "<>"
  t2 <- parse_term
  return (Con t t2)

parse_par :: ReadP Term
parse_par = do
  lexeme (char '(')
  choice
    [ parse_par_one
    , parse_par_term
    ]

parse_par_one :: ReadP Term
parse_par_one = do
  lexeme (char ')')
  return One

parse_par_term :: ReadP Term
parse_par_term = do
  t <- parse_term
  choice
    [ parse_par_tup t
    , parse_par_app t
    ]

parse_par_tup :: Term -> ReadP Term
parse_par_tup t = do
  lexeme (char ',')
  u <- parse_term
  lexeme (char ')')
  return (Tup t u)

parse_par_app :: Term -> ReadP Term
parse_par_app t = do
  ts <- many parse_term
  lexeme (char ')')
  return (foldl' App t ts)

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  lexeme (char 'λ')
  choice
    [ parse_lam_brace
    , parse_lam_var
    ]

parse_lam_brace :: ReadP Term
parse_lam_brace = do
  lexeme (char '{')
  t <- choice
    [ parse_get
    , parse_use
    , parse_if
    , parse_swi
    , parse_mat
    , return Efq
    ]
  lexeme (char '}')
  return t

parse_lam_var :: ReadP Term
parse_lam_var = do
  k <- parse_name
  lexeme (char '.')
  t <- parse_term
  return (Lam (name_to_int k) t)

parse_get :: ReadP Term
parse_get = do
  lexeme (char ',')
  lexeme (char ':')
  c <- parse_term
  optional (lexeme (char ';'))
  return (Get c)

parse_use :: ReadP Term
parse_use = do
  lexeme (string "()")
  lexeme (char ':')
  u <- parse_term
  optional (lexeme (char ';'))
  return (Use u)

parse_if :: ReadP Term
parse_if = do
  lexeme (string "#F")
  lexeme (char ':')
  f <- parse_term
  optional (lexeme (char ';'))
  lexeme (string "#T")
  lexeme (char ':')
  t <- parse_term
  optional (lexeme (char ';'))
  return (If f t)

parse_swi :: ReadP Term
parse_swi = do
  lexeme (char '0')
  lexeme (char ':')
  z <- parse_term
  optional (lexeme (char ';'))
  lexeme (string "1+")
  lexeme (char ':')
  s <- parse_term
  optional (lexeme (char ';'))
  return (Swi z s)

parse_mat :: ReadP Term
parse_mat = do
  lexeme (string "[]")
  lexeme (char ':')
  n <- parse_term
  optional (lexeme (char ';'))
  lexeme (string "<>")
  lexeme (char ':')
  c <- parse_term
  optional (lexeme (char ';'))
  return (Mat n c)

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

parse_set :: ReadP Term
parse_set = lexeme (char '*') >> return Set

parse_all :: ReadP Term
parse_all = do
  lexeme (char '∀')
  a <- parse_term_base
  lexeme (char '.')
  b <- parse_term
  return (All a b)

parse_sig :: ReadP Term
parse_sig = do
  lexeme (char 'Σ')
  a <- parse_term_base
  lexeme (char '.')
  b <- parse_term
  return (Sig a b)

parse_nat :: ReadP Term
parse_nat = lexeme (char 'ℕ') >> return Nat

parse_ref :: ReadP Term
parse_ref = do
  lexeme (char '@')
  k <- parse_name
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

parse_number :: ReadP Int
parse_number = read <$> munch1 isDigit

parse_var :: ReadP Term
parse_var = do
  k <- parse_name
  let kid = name_to_int k
  choice
    [ string "₀" >> return (Dp0 kid)
    , string "₁" >> return (Dp1 kid)
    , return (Var kid)
    ]

parse_emp :: ReadP Term
parse_emp = lexeme (char '⊥') >> return Emp

parse_uni :: ReadP Term
parse_uni = lexeme (char '⊤') >> return Uni

parse_bol :: ReadP Term
parse_bol = lexeme (char '𝔹') >> return Bol

parse_ctr :: ReadP Term
parse_ctr = do
  lexeme (char '#')
  choice
    [ char 'F' >> return Fal
    , char 'T' >> return Tru
    ]

parse_nil :: ReadP Term
parse_nil = do
  lexeme (string "[]")
  return Nil

parse_nam :: ReadP Term
parse_nam = do
  lexeme (char '^')
  choice
    [ parse_nam_dry
    , parse_nam_var
    ]

parse_nam_dry :: ReadP Term
parse_nam_dry = do
  lexeme (char '(')
  f <- parse_term
  x <- parse_term
  lexeme (char ')')
  return (Dry f x)

parse_nam_var :: ReadP Term
parse_nam_var = do
  k <- parse_name
  return (Nam k)

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
take_sub ki e k = taker (env_sub_map e) (k `shiftL` 2 + fromEnum ki)

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

make_auto_dup :: Env -> Name -> Lab -> Term -> IO ()
make_auto_dup e k l v = do
  k <- fresh e
  make_dup e k l v

subst :: Kind -> Env -> Name -> Term -> IO ()
subst s e k v = modifyIORef' (env_sub_map e) (IM.insert (k `shiftL` 2 + fromEnum s) v)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Dp0 k , Dp1 k)

-- WNF: Weak Normal Form
-- =====================

data Frame
  = FDp0   Name Lab -- ! F &L = _; F₀
  | FDp1   Name Lab -- ! F &L = _; F₁
  | FApp   Term     -- (_ x)
  | FAppF  Term     -- (λ{..} _)
  | FAppG  Term     -- ((f~>_) x)
  | FAppGF Term     -- ((f~>λ{..}) _)
  | FAnd   Term     -- (_ && b)
  | FEql   Term     -- (_ == b)
  | FEqlA  Term     -- (a == _)
  deriving Show

type Stack = [Frame]

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

type WnfDup    = Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
type WnfEql    = Env -> Stack -> Term -> Term -> IO Term
type WnfGuaSwi = Env -> Stack -> Term -> Term -> Term -> Term -> IO Term

wnf_enter :: Env -> Stack -> Term -> IO Term

wnf_enter e s (Var k) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Var k)
  wnf_sub VAR e s k

wnf_enter e s (Dp0 k) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Dp0 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub DP0 e s k

wnf_enter e s (Dp1 k) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Dp1 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub DP1 e s k

wnf_enter e s (App f x) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (App f x)
  wnf_enter e (FApp x : s) f

wnf_enter e s (And a b) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (And a b)
  wnf_enter e (FAnd b : s) a

wnf_enter e s (Eql a b) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Eql a b)
  wnf_enter e (FEql b : s) a

wnf_enter e s (Dup k l v t) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Dup k l v t)
  make_dup e k l v
  wnf_enter e s t

wnf_enter e s (Ref k) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Ref k)
  wnf_ref e s k

wnf_enter e s (Gua f g) = do
  when debug $ putStrLn $ "wnf_enter: " ++ show (Gua f g)
  wnf_unwind e s (Gua f g)

wnf_enter e s f = do
  when debug $ putStrLn $ "wnf_enter: " ++ show f
  wnf_unwind e s f

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []      v = return v
wnf_unwind e (x : s) v = do
  when debug $ putStrLn $ "wnf_unwind: " ++ show (x:s) ++ " | " ++ show v
  case x of
    FApp a           -> wnf_app e s v a
    FDp0 k l         -> wnf_dup e s v k l (Dp0 k)
    FDp1 k l         -> wnf_dup e s v k l (Dp1 k)
    FAnd b           -> wnf_and e s v b
    FEql b           -> wnf_eql e s v b
    FEqlA a          -> wnf_eql_x e s a v
    FAppF f          -> wnf_app_f e s f v
    FAppG (Tup f a)  -> wnf_app_gua e s f v a
    FAppGF (Tup f m) -> wnf_app_gua_f e s f m v
    _                -> error "BadFrame"

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  when debug $ putStrLn $ "wnf_sub: " ++ show (Var k)
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s $ case ki of
      VAR -> Var k
      DP0 -> Dp0 k
      DP1 -> Dp1 k

wnf_dup :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup e s v k l t = do
  when debug $ putStrLn $ "wnf_dup: " ++ show (Dup k l v t)
  case v of
    Era    -> wnf_dup_era e s v k l t
    Sup {} -> wnf_dup_sup e s v k l t
    Set    -> wnf_dup_set e s v k l t
    All {} -> wnf_dup_all e s v k l t
    Lam {} -> wnf_dup_lam e s v k l t
    Nat    -> wnf_dup_nat e s v k l t
    Zer    -> wnf_dup_zer e s v k l t
    Suc {} -> wnf_dup_suc e s v k l t
    Swi {} -> wnf_dup_swi e s v k l t
    Nam {} -> wnf_dup_nam e s v k l t
    Dry {} -> wnf_dup_dry e s v k l t
    Gua {} -> wnf_dup_gua e s v k l t
    Sig {} -> wnf_dup_sig e s v k l t
    Tup {} -> wnf_dup_tup e s v k l t
    Get {} -> wnf_dup_get e s v k l t
    Emp    -> wnf_dup_emp e s v k l t
    Efq    -> wnf_dup_efq e s v k l t
    Uni    -> wnf_dup_uni e s v k l t
    One    -> wnf_dup_one e s v k l t
    Use {} -> wnf_dup_use e s v k l t
    Bol    -> wnf_dup_bol e s v k l t
    Fal    -> wnf_dup_fal e s v k l t
    Tru    -> wnf_dup_tru e s v k l t
    If {}  -> wnf_dup_if  e s v k l t
    Lst {} -> wnf_dup_lst e s v k l t
    Nil    -> wnf_dup_nil e s v k l t
    Con {} -> wnf_dup_con e s v k l t
    Mat {} -> wnf_dup_mat e s v k l t
    _      -> wnf_unwind e s (Dup k l v t)

wnf_dup_0 :: Env -> Stack -> Name -> Term -> Term -> IO Term
wnf_dup_0 e s k v t = do
  inc_inters e
  subst DP0 e k v
  subst DP1 e k v
  wnf e s t

wnf_dup_1 :: Env -> Stack -> Name -> Lab -> Term -> Term -> (Term -> Term) -> IO Term
wnf_dup_1 e s k l t v1 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  subst DP0 e k (c v1a)
  subst DP1 e k (c v1b)
  wnf e s t

wnf_dup_2 :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> (Term -> Term -> Term) -> IO Term
wnf_dup_2 e s k l t v1 v2 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  (v2a, v2b) <- clone e l v2
  subst DP0 e k (c v1a v2a)
  subst DP1 e k (c v1b v2b)
  wnf e s t

wnf_dup_era :: WnfDup
wnf_dup_era e s Era k _ t = wnf_dup_0 e s k Era t

wnf_dup_sup :: WnfDup
wnf_dup_sup e s (Sup vl va vb) k l t
  | l == vl = do
      inc_inters e
      subst DP0 e k va
      subst DP1 e k vb
      wnf e s t
  | otherwise = do
      wnf_dup_2 e s k l t va vb (Sup vl)

wnf_dup_set :: WnfDup
wnf_dup_set e s Set k _ t = wnf_dup_0 e s k Set t

wnf_dup_all :: WnfDup
wnf_dup_all e s (All va vb) k l t = wnf_dup_2 e s k l t va vb All

wnf_dup_lam :: WnfDup
wnf_dup_lam e s (Lam vk vf) k l t = do
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst DP0 e k (Lam x0 g0)
  subst DP1 e k (Lam x1 g1)
  subst VAR e vk (Sup l (Var x0) (Var x1))
  wnf e s t

wnf_dup_nat :: WnfDup
wnf_dup_nat e s Nat k _ t = wnf_dup_0 e s k Nat t

wnf_dup_zer :: WnfDup
wnf_dup_zer e s Zer k _ t = wnf_dup_0 e s k Zer t

wnf_dup_suc :: WnfDup
wnf_dup_suc e s (Suc p) k l t = wnf_dup_1 e s k l t p Suc

wnf_dup_swi :: WnfDup
wnf_dup_swi e s (Swi vz vs) k l t = wnf_dup_2 e s k l t vz vs Swi

wnf_dup_nam :: WnfDup
wnf_dup_nam e s (Nam n) k _ t = wnf_dup_0 e s k (Nam n) t

wnf_dup_dry :: WnfDup
wnf_dup_dry e s (Dry vf vx) k l t = wnf_dup_2 e s k l t vf vx Dry

wnf_dup_gua :: WnfDup
wnf_dup_gua e s (Gua f g) k l t = wnf_dup_2 e s k l t f g Gua

wnf_dup_sig :: WnfDup
wnf_dup_sig e s (Sig a b) k l t = wnf_dup_2 e s k l t a b Sig

wnf_dup_tup :: WnfDup
wnf_dup_tup e s (Tup a b) k l t = wnf_dup_2 e s k l t a b Tup

wnf_dup_get :: WnfDup
wnf_dup_get e s (Get c) k l t = wnf_dup_1 e s k l t c Get

wnf_dup_emp :: WnfDup
wnf_dup_emp e s Emp k _ t = wnf_dup_0 e s k Emp t

wnf_dup_efq :: WnfDup
wnf_dup_efq e s Efq k _ t = wnf_dup_0 e s k Efq t

wnf_dup_uni :: WnfDup
wnf_dup_uni e s Uni k _ t = wnf_dup_0 e s k Uni t

wnf_dup_one :: WnfDup
wnf_dup_one e s One k _ t = wnf_dup_0 e s k One t

wnf_dup_use :: WnfDup
wnf_dup_use e s (Use u) k l t = wnf_dup_1 e s k l t u Use

wnf_dup_bol :: WnfDup
wnf_dup_bol e s Bol k _ t = wnf_dup_0 e s k Bol t

wnf_dup_fal :: WnfDup
wnf_dup_fal e s Fal k _ t = wnf_dup_0 e s k Fal t

wnf_dup_tru :: WnfDup
wnf_dup_tru e s Tru k _ t = wnf_dup_0 e s k Tru t

wnf_dup_if :: WnfDup
wnf_dup_if e s (If f tr) k l t = wnf_dup_2 e s k l t f tr If

wnf_dup_lst :: WnfDup
wnf_dup_lst e s (Lst x) k l t = wnf_dup_1 e s k l t x Lst

wnf_dup_nil :: WnfDup
wnf_dup_nil e s Nil k _ t = wnf_dup_0 e s k Nil t

wnf_dup_con :: WnfDup
wnf_dup_con e s (Con h tr) k l t = wnf_dup_2 e s k l t h tr Con

wnf_dup_mat :: WnfDup
wnf_dup_mat e s (Mat n c) k l t = wnf_dup_2 e s k l t n c Mat

wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s f a = do
  when debug $ putStrLn $ "wnf_app: " ++ show (App f a)
  case f of
    Era       -> wnf_app_era e s f a
    Sup {}    -> wnf_app_sup e s f a
    Lam {}    -> wnf_app_lam e s f a
    Nam {}    -> wnf_app_nam e s f a
    Dry {}    -> wnf_app_dry e s f a
    Swi {}    -> wnf_enter e (FAppF f : s) a
    Get {}    -> wnf_enter e (FAppF f : s) a
    Efq       -> wnf_enter e (FAppF f : s) a
    Use {}    -> wnf_enter e (FAppF f : s) a
    If {}     -> wnf_enter e (FAppF f : s) a
    Mat {}    -> wnf_enter e (FAppF f : s) a
    Gua f0 g0 -> wnf_enter e (FAppG (Tup f0 a) : s) g0
    _         -> wnf_unwind e s (App f a)

wnf_app_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_era e s Era v = do
  inc_inters e
  wnf e s Era

wnf_app_nam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_nam e s (Nam fk) v = wnf e s (Dry (Nam fk) v)

wnf_app_dry :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_dry e s (Dry ff fx) v = wnf e s (Dry (Dry ff fx) v)

wnf_app_lam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_lam e s (Lam fx ff) v = do
  inc_inters e
  subst VAR e fx v
  wnf e s ff

wnf_app_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_sup e s (Sup fL fa fb) v = do
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

wnf_app_f :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_f e s f a = case f of
  Swi {} -> wnf_app_swi e s f a
  Get {} -> wnf_app_get e s f a
  Efq    -> wnf_app_efq e s f a
  Use {} -> wnf_app_use e s f a
  If {}  -> wnf_app_if  e s f a
  Mat {} -> wnf_app_mat e s f a
  _      -> wnf_unwind e s (App f a)

wnf_app_swi :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi e s f@(Swi z sc) a = case a of
  Era    -> wnf_app_swi_era e s f a
  Sup {} -> wnf_app_swi_sup e s f a
  Zer    -> wnf_app_swi_zer e s f a
  Suc {} -> wnf_app_swi_suc e s f a
  _      -> wnf_unwind e s (App f a)

wnf_app_swi_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_era e s (Swi z sc) Era = do
  inc_inters e
  wnf e s Era

wnf_app_swi_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_sup e s (Swi z sc) (Sup l a b) = do
  inc_inters e
  (z0, z1) <- clone e l z
  (s0, s1) <- clone e l sc
  let app0 = App (Swi z0 s0) a
  let app1 = App (Swi z1 s1) b
  wnf_enter e s (Sup l app0 app1)

wnf_app_swi_zer :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_zer e s (Swi z sc) Zer = do
  inc_inters e
  wnf e s z

wnf_app_swi_suc :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_suc e s (Swi z sc) (Suc n) = do
  inc_inters e
  wnf_enter e s (App sc n)

wnf_app_get :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_get e s f@(Get c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Get c0) x) (App (Get c1) y))
  Tup x y -> do
    inc_inters e
    wnf_enter e s (App (App c x) y)
  _ -> wnf_unwind e s (App f a)

wnf_app_efq :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_efq e s Efq a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    wnf_enter e s (Sup l (App Efq x) (App Efq y))
  _ -> wnf_unwind e s (App Efq a)

wnf_app_use :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_use e s f@(Use u) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (u0, u1) <- clone e l u
    wnf_enter e s (Sup l (App (Use u0) x) (App (Use u1) y))
  One -> do
    inc_inters e
    wnf e s u
  _ -> wnf_unwind e s (App f a)

wnf_app_if :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_if e s f@(If ft ff) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (ft0, ft1) <- clone e l ft
    (ff0, ff1) <- clone e l ff
    wnf_enter e s (Sup l (App (If ft0 ff0) x) (App (If ft1 ff1) y))
  Fal -> do
    inc_inters e
    wnf e s ft
  Tru -> do
    inc_inters e
    wnf e s ff
  _ -> wnf_unwind e s (App f a)

wnf_app_mat :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_mat e s f@(Mat n c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (n0, n1) <- clone e l n
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Mat n0 c0) x) (App (Mat n1 c1) y))
  Nil -> do
    inc_inters e
    wnf e s n
  Con h t -> do
    inc_inters e
    wnf_enter e s (App (App c h) t)
  _ -> wnf_unwind e s (App f a)

wnf_app_gua :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua e s f g a = do
  case g of
    Era    -> wnf_app_gua_era e s f g a
    Sup {} -> wnf_app_gua_sup e s f g a
    Lam {} -> wnf_app_gua_lam e s f g a
    Swi {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Get {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Efq    -> wnf_enter e (FAppGF (Tup f g) : s) a
    Use {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    If {}  -> wnf_enter e (FAppGF (Tup f g) : s) a
    Mat {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Gua {} -> wnf_app_gua_gua e s f g a
    _      -> wnf_unwind e s (App (Tup f g) a)

wnf_app_gua_era :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_era e s f Era a = do
  inc_inters e
  wnf e s Era

wnf_app_gua_sup :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_sup e s f (Sup l x y) a = do
  inc_inters e
  (f0,f1) <- clone e l f
  (a0,a1) <- clone e l a
  let app0 = (App (Gua f0 x) a0)
  let app1 = (App (Gua f1 y) a1)
  wnf_enter e s (Sup l app0 app1)

wnf_app_gua_lam :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_lam e s f (Lam x g) a = do
  inc_inters e
  subst VAR e x a
  wnf_enter e s (Gua (App f (Var x)) g)

wnf_app_gua_gua :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_gua e s f g a = do
  inc_inters e
  wnf_enter e s (Gua (App f a) (App g a))

wnf_app_gua_f :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_f e s f m a = case m of
  Swi {} -> wnf_app_gua_swi e s f m a
  Get {} -> wnf_app_gua_get e s f m a
  Efq    -> wnf_app_gua_efq e s f m a
  Use {} -> wnf_app_gua_use e s f m a
  If {}  -> wnf_app_gua_if  e s f m a
  Mat {} -> wnf_app_gua_mat e s f m a
  _      -> wnf_unwind e s (App (Gua f m) a)

wnf_app_gua_swi :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_swi e s f (Swi z sc) a = case a of
  Era    -> wnf_app_gua_swi_era e s f z sc a
  Sup {} -> wnf_app_gua_swi_sup e s f z sc a
  Zer    -> wnf_app_gua_swi_zer e s f z sc a
  Suc {} -> wnf_app_gua_swi_suc e s f z sc a
  Gua {} -> wnf_app_gua_gua e s f (Swi z sc) a
  _      -> wnf_unwind e s (App f a)

wnf_app_gua_swi_era :: WnfGuaSwi
wnf_app_gua_swi_era e s f z sc Era = do
  wnf_enter e s Era

wnf_app_gua_swi_sup :: WnfGuaSwi
wnf_app_gua_swi_sup e s f z sc (Sup l a b) = do
  inc_inters e
  (f0,f1) <- clone e l f
  (z0,z1) <- clone e l z
  (s0,s1) <- clone e l sc
  let app0 = App (Gua f0 (Swi z0 s0)) a
  let app1 = App (Gua f1 (Swi z1 s1)) b
  wnf_enter e s (Sup l app0 app1)

wnf_app_gua_swi_zer :: WnfGuaSwi
wnf_app_gua_swi_zer e s f z sc Zer = do
  inc_inters e
  wnf_enter e s (Gua (App f Zer) z)

wnf_app_gua_swi_suc :: WnfGuaSwi
wnf_app_gua_swi_suc e s f z sc (Suc n) = do
  inc_inters e
  p <- fresh e
  let fn = (Lam p (App f (Suc (Var p))))
  wnf_enter e s (App (Gua fn sc) n)

wnf_app_gua_get :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_get e s f (Get c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Gua f0 (Get c0)) x) (App (Gua f1 (Get c1)) y))
  Tup x y -> do
    inc_inters e
    xV <- fresh e
    yV <- fresh e
    let fn = Lam xV (Lam yV (App f (Tup (Var xV) (Var yV))))
    wnf_enter e s (App (App (Gua fn c) x) y)
  Gua {} -> do
    wnf_app_gua_gua e s f (Get c) a
  _ -> wnf_unwind e s (App (Gua f (Get c)) a)

wnf_app_gua_efq :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_efq e s f Efq a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    wnf_enter e s (Sup l (App (Gua f0 Efq) x) (App (Gua f1 Efq) y))
  Gua {} -> do
    wnf_app_gua_gua e s f Efq a
  _ -> wnf_unwind e s (App (Gua f Efq) a)

wnf_app_gua_use :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_use e s f (Use u) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (u0, u1) <- clone e l u
    wnf_enter e s (Sup l (App (Gua f0 (Use u0)) x) (App (Gua f1 (Use u1)) y))
  One -> do
    inc_inters e
    wnf_enter e s (Gua (App f One) u)
  Gua {} -> do
    wnf_app_gua_gua e s f (Use u) a
  _ -> wnf_unwind e s (App (Gua f (Use u)) a)

wnf_app_gua_if :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_if e s f (If ft ff) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (ft0, ft1) <- clone e l ft
    (ff0, ff1) <- clone e l ff
    wnf_enter e s (Sup l (App (Gua f0 (If ft0 ff0)) x) (App (Gua f1 (If ft1 ff1)) y))
  Fal -> do
    inc_inters e
    wnf_enter e s (Gua (App f Fal) ft)
  Tru -> do
    inc_inters e
    wnf_enter e s (Gua (App f Tru) ff)
  Gua {} -> do
    wnf_app_gua_gua e s f (If ft ff) a
  _ -> wnf_unwind e s (App (Gua f (If ft ff)) a)

wnf_app_gua_mat :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat e s f (Mat n c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (n0, n1) <- clone e l n
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Gua f0 (Mat n0 c0)) x) (App (Gua f1 (Mat n1 c1)) y))
  Nil -> do
    inc_inters e
    wnf_enter e s (Gua (App f Nil) n)
  Con h t -> do
    inc_inters e
    hV <- fresh e
    tV <- fresh e
    let fn = Lam hV (Lam tV (App f (Con (Var hV) (Var tV))))
    wnf_enter e s (App (App (Gua fn c) h) t)
  Gua {} -> do
    wnf_app_gua_gua e s f (Mat n c) a
  _ -> wnf_unwind e s (App (Gua f (Mat n c)) a)

wnf_and :: Env -> Stack -> Term -> Term -> IO Term
wnf_and e s a b =  do
  case a of
    Era    -> wnf_and_era e s a b
    Sup {} -> wnf_and_sup e s a b
    Fal    -> wnf_and_fal e s a b
    Tru    -> wnf_and_tru e s a b
    _      -> wnf_unwind e s (And a b)

wnf_and_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_era e s Era b = do
  inc_inters e
  wnf e s Era

wnf_and_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_sup e s (Sup l a0 a1) b = do
  inc_inters e
  (b0, b1) <- clone e l b
  wnf_enter e s (Sup l (And a0 b0) (And a1 b1))

wnf_and_fal :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_fal e s Fal b = do
  inc_inters e
  wnf e s Fal

wnf_and_tru :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_tru e s Tru b = do
  inc_inters e
  wnf e s b

wnf_eql :: WnfEql
wnf_eql e s a b = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l a0 a1 -> do
    inc_inters e
    k <- fresh e
    make_dup e k l b
    wnf_enter e s (Sup l (Eql a0 (Dp0 k)) (Eql a1 (Dp1 k)))
  _ -> do
    wnf_enter e (FEqlA a : s) b

wnf_eql_x :: WnfEql
wnf_eql_x e s a b = case b of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l b0 b1 -> do
    inc_inters e
    k <- fresh e
    make_dup e k l a
    wnf_enter e s (Sup l (Eql (Dp0 k) b0) (Eql (Dp1 k) b1))
  _ -> do
    wnf_eql_val e s a b

wnf_eql_val :: WnfEql
wnf_eql_val e s a b = case (a, b) of
  (Set, Set)       -> wnf_eql_set_set e s a b
  (All {}, All {}) -> wnf_eql_all_all e s a b
  (Lam {}, Lam {}) -> wnf_eql_lam_lam e s a b
  (Sig {}, Sig {}) -> wnf_eql_sig_sig e s a b
  (Tup {}, Tup {}) -> wnf_eql_tup_tup e s a b
  (Get {}, Get {}) -> wnf_eql_get_get e s a b
  (Emp, Emp)       -> wnf_eql_emp_emp e s a b
  (Efq, Efq)       -> wnf_eql_efq_efq e s a b
  (Uni, Uni)       -> wnf_eql_uni_uni e s a b
  (One, One)       -> wnf_eql_one_one e s a b
  (Use {}, Use {}) -> wnf_eql_use_use e s a b
  (Bol, Bol)       -> wnf_eql_bol_bol e s a b
  (Fal, Fal)       -> wnf_eql_fal_fal e s a b
  (Tru, Tru)       -> wnf_eql_tru_tru e s a b
  (Fal, Tru)       -> wnf_eql_fal_tru e s a b
  (Tru, Fal)       -> wnf_eql_tru_fal e s a b
  (If {}, If {})   -> wnf_eql_if_if   e s a b
  (Nat, Nat)       -> wnf_eql_nat_nat e s a b
  (Zer, Zer)       -> wnf_eql_zer_zer e s a b
  (Suc {}, Suc {}) -> wnf_eql_suc_suc e s a b
  (Swi {}, Swi {}) -> wnf_eql_swi_swi e s a b
  (Lst {}, Lst {}) -> wnf_eql_lst_lst e s a b
  (Nil, Nil)       -> wnf_eql_nil_nil e s a b
  (Con {}, Con {}) -> wnf_eql_con_con e s a b
  (Mat {}, Mat {}) -> wnf_eql_mat_mat e s a b
  (Nam {}, Nam {}) -> wnf_eql_nam_nam e s a b
  (Dry {}, Dry {}) -> wnf_eql_dry_dry e s a b
  _                -> wnf_eql_default e s a b

wnf_eql_set_set :: WnfEql
wnf_eql_set_set e s Set Set = do
  inc_inters e
  wnf e s Tru

wnf_eql_all_all :: WnfEql
wnf_eql_all_all e s (All aA aB) (All bA bB) = do
  inc_inters e
  wnf_enter e s (And (Eql aA bA) (Eql aB bB))

wnf_eql_lam_lam :: WnfEql
wnf_eql_lam_lam e s (Lam ax af) (Lam bx bf) = do
  inc_inters e
  x <- fresh e
  subst VAR e ax (Nam (int_to_name x))
  subst VAR e bx (Nam (int_to_name x))
  wnf_enter e s (Eql af bf)

wnf_eql_sig_sig :: WnfEql
wnf_eql_sig_sig e s (Sig aA aB) (Sig bA bB) = do
  inc_inters e
  wnf_enter e s (And (Eql aA bA) (Eql aB bB))

wnf_eql_tup_tup :: WnfEql
wnf_eql_tup_tup e s (Tup a1 a2) (Tup b1 b2) = do
  inc_inters e
  wnf_enter e s (And (Eql a1 b1) (Eql a2 b2))

wnf_eql_get_get :: WnfEql
wnf_eql_get_get e s (Get ac) (Get bc) = do
  inc_inters e
  wnf_enter e s (Eql ac bc)

wnf_eql_emp_emp :: WnfEql
wnf_eql_emp_emp e s Emp Emp = do
  inc_inters e
  wnf e s Tru

wnf_eql_efq_efq :: WnfEql
wnf_eql_efq_efq e s Efq Efq = do
  inc_inters e
  wnf e s Tru

wnf_eql_uni_uni :: WnfEql
wnf_eql_uni_uni e s Uni Uni = do
  inc_inters e
  wnf e s Tru

wnf_eql_one_one :: WnfEql
wnf_eql_one_one e s One One = do
  inc_inters e
  wnf e s Tru

wnf_eql_use_use :: WnfEql
wnf_eql_use_use e s (Use au) (Use bu) = do
  inc_inters e
  wnf_enter e s (Eql au bu)

wnf_eql_bol_bol :: WnfEql
wnf_eql_bol_bol e s Bol Bol = do
  inc_inters e
  wnf e s Tru

wnf_eql_fal_fal :: WnfEql
wnf_eql_fal_fal e s Fal Fal = do
  inc_inters e
  wnf e s Tru

wnf_eql_tru_tru :: WnfEql
wnf_eql_tru_tru e s Tru Tru = do
  inc_inters e
  wnf e s Tru

wnf_eql_fal_tru :: WnfEql
wnf_eql_fal_tru e s Fal Tru = do
  inc_inters e
  wnf e s Fal

wnf_eql_tru_fal :: WnfEql
wnf_eql_tru_fal e s Tru Fal = do
  inc_inters e
  wnf e s Fal

wnf_eql_if_if :: WnfEql
wnf_eql_if_if e s (If af at) (If bf bt) = do
  inc_inters e
  wnf_enter e s (And (Eql af bf) (Eql at bt))

wnf_eql_nat_nat :: WnfEql
wnf_eql_nat_nat e s Nat Nat = do
  inc_inters e
  wnf e s Tru

wnf_eql_zer_zer :: WnfEql
wnf_eql_zer_zer e s Zer Zer = do
  inc_inters e
  wnf e s Tru

wnf_eql_suc_suc :: WnfEql
wnf_eql_suc_suc e s (Suc a) (Suc b) = do
  inc_inters e
  wnf_enter e s (Eql a b)

wnf_eql_swi_swi :: WnfEql
wnf_eql_swi_swi e s (Swi az as) (Swi bz bs) = do
  inc_inters e
  wnf_enter e s (And (Eql az bz) (Eql as bs))

wnf_eql_lst_lst :: WnfEql
wnf_eql_lst_lst e s (Lst aT) (Lst bT) = do
  inc_inters e
  wnf_enter e s (Eql aT bT)

wnf_eql_nil_nil :: WnfEql
wnf_eql_nil_nil e s Nil Nil = do
  inc_inters e
  wnf e s Tru

wnf_eql_con_con :: WnfEql
wnf_eql_con_con e s (Con ah at) (Con bh bt) = do
  inc_inters e
  wnf_enter e s (And (Eql ah bh) (Eql at bt))

wnf_eql_mat_mat :: WnfEql
wnf_eql_mat_mat e s (Mat an ac) (Mat bn bc) = do
  inc_inters e
  wnf_enter e s (And (Eql an bn) (Eql ac bc))

wnf_eql_nam_nam :: WnfEql
wnf_eql_nam_nam e s (Nam x) (Nam y) = do
  inc_inters e
  if x == y then
    wnf e s Tru
  else
    wnf e s Fal

wnf_eql_dry_dry :: WnfEql
wnf_eql_dry_dry e s (Dry af ax) (Dry bf bx) = do
  inc_inters e
  wnf_enter e s (And (Eql af bf) (Eql ax bx))

wnf_eql_default :: WnfEql
wnf_eql_default e s a b = do
  wnf e s Fal

wnf_ref :: Env -> Stack -> Name -> IO Term
wnf_ref e s k = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- alloc e f
      wnf_enter e s g
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

-- Allocation
-- ==========

-- Allocates a closed term, replacing all bound names with fresh ones.
alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where

  go :: IM.IntMap Name -> Term -> IO Term

  go m (Var k) = do
    return $ Var (IM.findWithDefault k k m)

  go m (Dp0 k) = do
    return $ Dp0 (IM.findWithDefault k k m)

  go m (Dp1 k) = do
    return $ Dp1 (IM.findWithDefault k k m)

  go _ Era = do
    return Era

  go m (Sup l a b) = do
    a' <- go m a
    b' <- go m b
    return $ Sup l a' b'

  go _ Set = do
    return Set

  go m (All a b) = do
    a' <- go m a
    b' <- go m b
    return $ All a' b'

  go m (App f x) = do
    f' <- go m f
    x' <- go m x
    return $ App f' x'

  go _ Nat = do
    return Nat

  go _ Zer = do
    return Zer

  go m (Suc n) = do
    n' <- go m n
    return $ Suc n'

  go m (Swi z s) = do
    z' <- go m z
    s' <- go m s
    return $ Swi z' s'

  go m (And a b) = do
    a' <- go m a
    b' <- go m b
    return $ And a' b'

  go m (Eql a b) = do
    a' <- go m a
    b' <- go m b
    return $ Eql a' b'

  go _ (Ref k) = do
    return $ Ref k

  go _ (Nam k) = do
    return $ Nam k

  go m (Dry f x) = do
    f' <- go m f
    x' <- go m x
    return $ Dry f' x'

  go m (Gua f g) = do
    f' <- go m f
    g' <- go m g
    return $ Gua f' g'

  go m (Sig a b) = do
    a' <- go m a
    b' <- go m b
    return $ Sig a' b'

  go m (Tup a b) = do
    a' <- go m a
    b' <- go m b
    return $ Tup a' b'

  go m (Get c) = do
    c' <- go m c
    return $ Get c'

  go _ Emp = do
    return Emp

  go _ Efq = do
    return Efq

  go _ Uni = do
    return Uni

  go _ One = do
    return One

  go m (Use u) = do
    u' <- go m u
    return $ Use u'

  go _ Bol = do
    return Bol

  go _ Fal = do
    return Fal

  go _ Tru = do
    return Tru

  go m (If f t) = do
    f' <- go m f
    t' <- go m t
    return $ If f' t'

  go m (Lst t) = do
    t' <- go m t
    return $ Lst t'

  go _ Nil = do
    return Nil

  go m (Con h t) = do
    h' <- go m h
    t' <- go m t
    return $ Con h' t'

  go m (Mat n c) = do
    n' <- go m n
    c' <- go m c
    return $ Mat n' c'

  go m (Dup k l v t) = do
    k' <- fresh e
    v' <- go m v
    t' <- go (IM.insert k k' m) t
    return $ Dup k' l v' t'

  go m (Lam k f) = do
    k' <- fresh e
    f' <- go (IM.insert k k' m) f
    return $ Lam k' f'

-- Normalization
-- =============

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x' <- wnf e [] x
  case x' of

    Var k -> do
      return $ Var k

    Dp0 k -> do
      return $ Dp0 k

    Dp1 k -> do
      return $ Dp1 k

    Era -> do
      return $ Era

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

    Set -> do
      return $ Set

    All a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ All a' b'

    Lam k f -> do
      subst VAR e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'

    App f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ App f' x'

    Nat -> do
      return $ Nat

    Zer -> do
      return $ Zer

    Suc p -> do
      p' <- snf e d p
      return $ Suc p'

    Swi z s -> do
      z' <- snf e d z
      s' <- snf e d s
      return $ Swi z' s'

    And a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ And a' b'

    Eql a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Eql a' b'

    Ref k -> do
      return $ Ref k

    Nam k -> do
      return $ Nam k

    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'

    Gua f g -> do
      g' <- snf e d g
      return $ g'

    Sig a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Sig a' b'

    Tup a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Tup a' b'

    Get c -> do
      c' <- snf e d c
      return $ Get c'

    Emp -> do
      return $ Emp

    Efq -> do
      return $ Efq

    Uni -> do
      return $ Uni

    One -> do
      return $ One

    Use u -> do
      u' <- snf e d u
      return $ Use u'

    Bol -> do
      return $ Bol

    Fal -> do
      return $ Fal

    Tru -> do
      return $ Tru

    If f t -> do
      f' <- snf e d f
      t' <- snf e d t
      return $ If f' t'

    Lst t -> do
      t' <- snf e d t
      return $ Lst t'

    Nil -> do
      return $ Nil

    Con h t -> do
      h' <- snf e d h
      t' <- snf e d t
      return $ Con h' t'

    Mat n c -> do
      n' <- snf e d n
      c' <- snf e d c
      return $ Mat n' c'

-- Collapsing
-- ==========

collapse :: Env -> Term -> IO Term
collapse e x = do
  !x <- wnf e [] x
  case x of

    Era -> do
      return Era

    (Sup l a b) -> do
      a' <- collapse e a
      b' <- collapse e b
      return $ Sup l a' b'

    Set -> do
      return Set

    All a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inject e (Lam aV (Lam bV (All (Var aV) (Var bV)))) (Con a' (Con b' Nil))

    (Lam k f) -> do
      fV <- fresh e
      f' <- collapse e f
      inject e (Lam fV (Lam k (Var fV))) (Con f' Nil)

    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (App (Var fV) (Var xV)))) (Con f' (Con x' Nil))

    Nat -> do
      return Nat

    Zer -> do
      return Zer

    (Suc p) -> do
      pV <- fresh e
      p' <- collapse e p
      inject e (Lam pV (Suc (Var pV))) (Con p' Nil)

    (Swi z s) -> do
      zV <- fresh e
      sV <- fresh e
      z' <- collapse e z
      s' <- collapse e s
      inject e (Lam zV (Lam sV (Swi (Var zV) (Var sV)))) (Con z' (Con s' Nil))

    (And a b) -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inject e (Lam aV (Lam bV (And (Var aV) (Var bV)))) (Con a' (Con b' Nil))

    (Eql a b) -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inject e (Lam aV (Lam bV (Eql (Var aV) (Var bV)))) (Con a' (Con b' Nil))

    Nam n -> do
      return $ Nam n

    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) (Con f' (Con x' Nil))

    (Gua f g) -> do
      collapse e g

    Sig a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inject e (Lam aV (Lam bV (Sig (Var aV) (Var bV)))) (Con a' (Con b' Nil))

    Tup a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inject e (Lam aV (Lam bV (Tup (Var aV) (Var bV)))) (Con a' (Con b' Nil))

    Get c -> do
      cV <- fresh e
      c' <- collapse e c
      inject e (Lam cV (Get (Var cV))) (Con c' Nil)

    Emp -> do
      return Emp

    Efq -> do
      return Efq

    Uni -> do
      return Uni

    One -> do
      return One

    Use u -> do
      uV <- fresh e
      u' <- collapse e u
      inject e (Lam uV (Use (Var uV))) (Con u' Nil)

    Bol -> do
      return Bol

    Fal -> do
      return Fal

    Tru -> do
      return Tru

    If f t -> do
      fV <- fresh e
      tV <- fresh e
      f' <- collapse e f
      t' <- collapse e t
      inject e (Lam fV (Lam tV (If (Var fV) (Var tV)))) (Con f' (Con t' Nil))

    Lst t -> do
      tV <- fresh e
      t' <- collapse e t
      inject e (Lam tV (Lst (Var tV))) (Con t' Nil)

    Nil -> do
      return Nil

    Con h t -> do
      hV <- fresh e
      tV <- fresh e
      h' <- collapse e h
      t' <- collapse e t
      inject e (Lam hV (Lam tV (Con (Var hV) (Var tV)))) (Con h' (Con t' Nil))

    Mat n c -> do
      nV <- fresh e
      cV <- fresh e
      n' <- collapse e n
      c' <- collapse e c
      inject e (Lam nV (Lam cV (Mat (Var nV) (Var cV)))) (Con n' (Con c' Nil))

    x -> do
      return $ x

inject :: Env -> Term -> Term -> IO Term
inject e f xs = do
  !xs <- wnf e [] xs
  case xs of
    Era -> do
      error "TODO"
    Sup xsl xsa xsb -> do
      error "TODO"
    Nil -> do
      return $ f
    Con h t -> do
      !h <- wnf e [] h
      case h of
        (Sup l a b) -> do
          (f0,f1) <- clone e l f
          (t0,t1) <- clone e l t
          a <- inject e f0 (Con a t0)
          b <- inject e f1 (Con b t1)
          return $ Sup l a b
        h -> do
          inject e (App f h) t

flatten :: Term -> [Term]
flatten term = bfs [term] [] where
  bfs []     acc = reverse acc
  bfs (t:ts) acc = case t of
    Sup _ a b -> bfs (ts ++ [a, b]) acc
    _         -> bfs ts (t : acc)

-- Tests
-- =====

f :: Int -> String
f n = "λf." ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00&A=f;"
  dup i = "!F" ++ pad i ++ "&A=λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));"
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

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
  , "@id  = ^id ~> λa.a"
  , "@not = ^not ~> λ{0:1+0;1+:λp.0}"
  , "@dbl = ^dbl ~> λ{0:0;1+:λp.1+1+(@dbl p)}"
  , "@and = ^and ~> λ{0:λ{0:0;1+:λp.0};1+:λp.λ{0:0;1+:λp.1+0}}"
  , "@add = ^add ~> λ{0:λb.b;1+:λa.λb.1+(@add a b)}"
  , "@sum = ^sum ~> λ{0:0;1+:λp.!P&S=p;1+(@add P₀ (@sum P₁))}"
  , "@foo = ^foo ~> &L{λx.x,λ{0:0;1+:λp.p}}"
  , "@gen = ^gen ~> !F&A=@gen &A{λx.!X&B=x;&B{X₀,1+X₁},λ{0:&C{0,1};1+:λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  , "@prd = ^prd ~> λ{0:0;1+:λp.p}"
  ]

tests :: [(String,String)]
tests =
  [ ("0", "0")
  , ("(@not 0)", "1")
  , ("(@not 1+0)", "0")
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(and 0 a)")
  , ("λx.(@and x 0)", "λa.(and a 0)")
  , ("(@sum 1+1+1+0)", "6")
  , ("λx.(@sum 1+1+1+x)", "λa.3+(add a 2+(add a 1+(add a (sum a))))")
  , ("(@foo 0)", "&L{0,0}")
  , ("(@foo 1+1+1+0)", "&L{3,2}")
  , ("λx.(@dbl 1+1+x)", "λa.4+(dbl a)")
  , ("("++f 2++" λX.(X λT0.λF0.F0 λT1.λF1.T1) λT2.λF2.T2)", "λa.λb.a")
  , ("1+&L{0,1}", "&L{1,2}")
  , ("1+&A{&B{0,1},&C{2,3}}", "&A{&B{1,2},&C{3,4}}")
  , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  , ("λa.λb.!A&L=a;!B&L=b;&L{λx.(x A₀ B₀),λx.(x A₁ B₁)}", "&L{λa.λb.λc.(c a b),λa.λb.λc.(c a b)}")
  , ("λt.(t &A{1,2} 3)", "&A{λa.(a 1 3),λa.(a 2 3)}")
  , ("λt.(t 1 &B{3,4})", "&B{λa.(a 1 3),λa.(a 1 4)}")
  , ("λt.(t &A{1,2} &A{3,4})", "&A{λa.(a 1 3),λa.(a 2 4)}")
  , ("λt.(t &A{1,2} &B{3,4})", "&A{&B{λa.(a 1 3),λa.(a 1 4)},&B{λa.(a 2 3),λa.(a 2 4)}}")
  , ("@gen", "&A{&B{λa.a,λa.1+a},&C{&D{λ{0:0;1+:λa.(gen a)},&E{λ{0:0;1+:λa.1+(gen a)},λ{0:0;1+:λa.2+(gen a)}}},&D{λ{0:1;1+:λa.(gen a)},&E{λ{0:1;1+:λa.1+(gen a)},λ{0:1;1+:λa.2+(gen a)}}}}}")
  , ("λx.(@gen 2+x)", "&A{&B{λa.2+a,λa.3+a},&D{λa.(gen a),&E{λa.2+(gen a),λa.4+(gen a)}}}")
  , ("(@gen 2)", "&A{&B{2,3},&D{&C{0,1},&E{&C{2,3},&C{4,5}}}}")
  , ("!f&DUP=@prd; (f₀ (f₁ 0))", "0")
  , ("2 == 2", "#T")
  , ("3 == 2", "#F")
  , ("(λa.λb.a) == (λx.λy.x)", "#T")
  , ("(λa.λb.a) == (λx.λy.y)", "#F")
  , ("(λx.2+x) == (λy.2+y)", "#T")
  , ("(λx.3+x) == (λy.2+y)", "#F")
  , ("#F && #F", "#F")
  , ("#F && #T", "#F")
  , ("#T && #F", "#F")
  , ("#T && #T", "#T")
  , ("(λt.(t (λa.2+a) (λb.2+b))) == (λu.(u (λx.2+x) (λy.2+y)))", "#T")
  , ("(λt.(t (λa.2+a) (λb.2+b))) == (λu.(u (λx.2+x) (λy.3+y)))", "#F")
  , ("(@NOT @T)", "λa.λb.b")
  , ("(@NOT (@NOT @T))", "λa.λb.a")
  , ("(@C2 @NOT @T)", "λa.λb.a")
  , ("@C2", "λa.λb.(a (a b))")
  , ("(@ADD @C2 @C1)", "λa.λb.(a (a (a b)))")
  , ("(@ADD @C1 λf.λx.(f x) @NOT)", "λa.λb.λc.(a b c)")
  , ("(@ADD @C1 @C1 @NOT)", "λa.λb.λc.(a b c)")
  , ("(@ADD @C2 @C2)", "λa.λb.(a (a (a (a b))))")
  , ("(@ADD @C4 @C1)", "λa.λb.(a (a (a (a (a b)))))")
  , ("(@ADD @C1 @C4)", "λa.λb.(a (a (a (a (a b)))))")
  , ("(@ADD @C4 @C4)", "λa.λb.(a (a (a (a (a (a (a (a b))))))))")
  , ("(@ADD @C1 @C4 @NOT @T)", "λa.λb.b")
  , ("(@ADD @C4 @C1 @NOT @T)", "λa.λb.b")
  , ("(@ADD @C2 @C4 @NOT @T)", "λa.λb.a")
  , ("(@ADD @C4 @C2 @NOT @T)", "λa.λb.a")
  , ("(@MUL @C4 @C2)", "λa.λb.(a (a (a (a (a (a (a (a b))))))))")
  , ("(@MUL @C4 @C4)", "λa.λb.(a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))))")
  , ("(@MUL @C4 @C2 @NOT @T)", "λa.λb.a")
  , ("(@MUL @C4 @C4 @NOT @T)", "λa.λb.a")
  , ("(@EXP @C4 @K2)", "λa.λb.(a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))))")
  , ("(@C8 @K8 @NOT @T)", "λa.λb.a")
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
