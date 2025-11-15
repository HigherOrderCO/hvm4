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
debug = True

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

data Func
  = FAbs !Name !Func
  | FSwi !Func !Func
  | FFrk !Name !Func !Func
  | FDel
  | FRet !Term
  deriving (Eq, Show)

data Kind
  = VAR
  | DP0
  | DP1
  deriving (Enum)

data Book = Book (M.Map Name Func)

data Dir
  = D0
  | D1
  deriving (Eq, Show)

type Path = [(Lab, Dir)]
type Subs = IM.IntMap Term

data Env = Env
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_sub_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

data Spine = Spine Int ([Term] -> Term)

instance Show Spine where
  show (Spine k f) = show (f (replicate k (Nam "_")))

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
show_func (FAbs k f)   = "Λ" ++ int_to_name k ++ "." ++ show_func f
show_func (FSwi z s)   = "Λ{0:" ++ show_func z ++ ";1+:" ++ show_func s ++ "}"
show_func (FFrk k a b) = "&" ++ int_to_name k ++ "{" ++ show_func a ++ "," ++ show_func b ++ "}"
show_func FDel         = "&{}"
show_func (FRet t)     = show t

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

parse_nam :: ReadP String
parse_nam = lexeme $ do
  head <- satisfy (`elem` alphabet_first)
  tail <- munch (`elem` alphabet)
  return (head : tail)

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
  let (t:rest) = ts
  return (foldl' App t rest)

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

parse_number :: ReadP Int
parse_number = read <$> munch1 isDigit

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

parse_func :: ReadP Func
parse_func = lexeme $ choice
  [ parse_fabs
  , parse_fswi
  , parse_fdel
  , parse_ffrk
  , FRet <$> parse_term
  ]

parse_fabs :: ReadP Func
parse_fabs = do
  lexeme (char 'Λ')
  k <- parse_nam
  lexeme (char '.')
  body <- parse_func
  return (FAbs (name_to_int k) body)

parse_fswi :: ReadP Func
parse_fswi = do
  lexeme (char 'Λ')
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "0:")
    z <- parse_func
    optional (lexeme (char ';'))
    lexeme (string "1+:")
    s <- parse_func
    return (FSwi z s)

parse_fdel :: ReadP Func
parse_fdel = lexeme (string "&{}") >> return FDel

parse_ffrk :: ReadP Func
parse_ffrk = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_func
    optional (lexeme (char ','))
    b <- parse_func
    return (FFrk (name_to_int l) a b)

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
    Nothing -> do
      return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = taker (env_dup_map e) k

take_sub :: Kind -> Env -> Name -> IO (Maybe Term)
take_sub ki e k = taker (env_sub_map e) (k `shiftL` 2 + fromEnum ki)

subst :: Kind -> Env -> Name -> Term -> IO ()
subst s e k v = modifyIORef' (env_sub_map e) (IM.insert (k `shiftL` 2 + fromEnum s) v)

duply :: Env -> Name -> Lab -> Term -> IO ()
duply e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  duply e k l v
  return $ (Dp0 k , Dp1 k)

clones :: Env -> Lab -> [Term] -> IO ([Term],[Term])
clones e l []       = return $ ([],[])
clones e l (x : xs) = do
  (x0  , x1 ) <- clone  e l x
  (xs0 , xs1) <- clones e l xs
  return $ (x0 : xs0 , x1 : xs1)

-- Spine
-- =====

spine_new :: Name -> Spine
spine_new k = Spine 0 (\_ -> Ref k)

spine_add_arg :: Spine -> Term -> Spine
spine_add_arg (Spine k f) x = Spine k (\ hs -> App (f hs) x)

spine_add_suc :: Spine -> Spine
spine_add_suc (Spine k f) = Spine (k+1) (\ (h:hs) -> App (f hs) (Suc h))

spine_term_val :: Spine -> Term
spine_term_val (Spine k f) = f (replicate k (Nam "_"))

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
wnf_unwind e []    v = return v
wnf_unwind e (x:s) v = do
  when debug $ putStrLn $ ">> wnf_unwind           : " ++ show v
  case x of
    FApp x -> case v of
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
      f            -> wnf_unwind e s (App f x)
    _ -> case v of
      Era          -> wnf_dpn_era e s k l          r
      Sup vl va vb -> wnf_dpn_sup e s k l vl va vb r
      Set          -> wnf_dpn_set e s k l          r
      All va vb    -> wnf_dpn_all e s k l va vb    r
      Lam vk vf    -> wnf_dpn_lam e s k l vk vf    r
      Nat          -> wnf_dpn_nat e s k l          r
      Zer          -> wnf_dpn_zer e s k l          r
      Suc vp       -> wnf_dpn_suc e s k l vp       r
      Nam vk       -> wnf_dpn_nam e s k l vk       r
      Dry vf vx    -> wnf_dpn_dry e s k l vf vx    r
      val          -> wnf_unwind  e s (Dup k l val r)
      where (k,l,r) = case x of { FDp0 k l -> (k,l,Dp0 k) ; FDp1 k l -> (k,l,Dp1 k) }

-- WNF: Interactions
-- -----------------

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  when debug $ putStrLn $ "## wnf_sub              : " ++ int_to_name k
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s $ var ki
      where var VAR = Var k
            var DP0 = Dp0 k
            var DP1 = Dp1 k

wnf_app_era :: Env -> Stack -> Term -> IO Term
wnf_app_era e s v = do
  when debug $ putStrLn $ "## wnf_app_era          : " ++ show (App Era v)
  inc_inters e
  wnf e s Era

wnf_app_set :: Env -> Stack -> Term -> IO Term
wnf_app_set e s v = do
  when debug $ putStrLn $ "## wnf_app_set          : " ++ show (App Set v)
  error "app-set"

wnf_app_all :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_all e s va vb v = do
  when debug $ putStrLn $ "## wnf_app_all          : " ++ show (App (All va vb) v)
  error "app-all"

wnf_app_nat :: Env -> Stack -> Term -> IO Term
wnf_app_nat e s v = do
  when debug $ putStrLn $ "## wnf_app_nat          : " ++ show (App Nat v)
  error "app-nat"

wnf_app_zer :: Env -> Stack -> Term -> IO Term
wnf_app_zer e s v = do
  when debug $ putStrLn $ "## wnf_app_zer          : " ++ show (App Zer v)
  error "app-zer"

wnf_app_suc :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_suc e s vp v = do
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

wnf_dpn_era :: Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_era e s k _ t = do
  when debug $ putStrLn $ "## wnf_dpn_era          : " ++ show (Dup k (name_to_int "_") Era t)
  inc_inters e
  subst DP0 e k Era
  subst DP1 e k Era
  wnf e s t

wnf_dpn_sup :: Env -> Stack -> Name -> Lab -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_sup e s k l vl va vb t
  | l == vl = do
      when debug $ putStrLn $ "## wnf_dpn_sup_same     : " ++ show (Dup k l (Sup vl va vb) t)
      inc_inters e
      subst DP0 e k va
      subst DP1 e k vb
      wnf e s t
  | otherwise = do
      when debug $ putStrLn $ "## wnf_dpn_sup_diff     : " ++ show (Dup k l (Sup vl va vb) t)
      inc_inters e
      (a0,a1) <- clone e l va
      (b0,b1) <- clone e l vb
      subst DP0 e k (Sup vl a0 b0)
      subst DP1 e k (Sup vl a1 b1)
      wnf e s t

wnf_dpn_set :: Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_set e s k _ t = do
  when debug $ putStrLn $ "## wnf_dpn_set          : " ++ show (Dup k (name_to_int "_") Set t)
  inc_inters e
  subst DP0 e k Set
  subst DP1 e k Set
  wnf e s t

wnf_dpn_all :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_all e s k l va vb t = do
  when debug $ putStrLn $ "## wnf_dpn_all          : " ++ show (Dup k l (All va vb) t)
  inc_inters e
  (a0,a1) <- clone e l va
  (b0,b1) <- clone e l vb
  subst DP0 e k (All a0 b0)
  subst DP1 e k (All a1 b1)
  wnf e s t

wnf_dpn_lam :: Env -> Stack -> Name -> Lab -> Name -> Term -> Term -> IO Term
wnf_dpn_lam e s k l vk vf t = do
  when debug $ putStrLn $ "## wnf_dpn_lam          : " ++ show (Dup k l (Lam vk vf) t)
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst DP0 e k (Lam x0 g0)
  subst DP1 e k (Lam x1 g1)
  subst VAR e vk (Sup l (Var x0) (Var x1))
  wnf e s t

wnf_dpn_nat :: Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_nat e s k _ t = do
  when debug $ putStrLn $ "## wnf_dpn_nat          : " ++ show (Dup k (name_to_int "_") Nat t)
  inc_inters e
  subst DP0 e k Nat
  subst DP1 e k Nat
  wnf e s t

wnf_dpn_zer :: Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_zer e s k _ t = do
  when debug $ putStrLn $ "## wnf_dpn_zer          : " ++ show (Dup k (name_to_int "_") Zer t)
  inc_inters e
  subst DP0 e k Zer
  subst DP1 e k Zer
  wnf e s t

wnf_dpn_suc :: Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnf_dpn_suc e s k l p t = do
  when debug $ putStrLn $ "## wnf_dpn_suc          : " ++ show (Dup k l (Suc p) t)
  inc_inters e
  (n0,n1) <- clone e l p
  subst DP0 e k (Suc n0)
  subst DP1 e k (Suc n1)
  wnf e s t

wnf_dpn_nam :: Env -> Stack -> Name -> Lab -> String -> Term -> IO Term
wnf_dpn_nam e s k _ n t = do
  when debug $ putStrLn $ "## wnf_dpn_nam          : " ++ show (Dup k (name_to_int "_") (Nam n) t)
  inc_inters e
  subst DP0 e k (Nam n)
  subst DP1 e k (Nam n)
  wnf e s t

wnf_dpn_dry :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_dry e s k l vf vx t = do
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
wnf_ref_apply e f x s m p = do
  when debug $ putStrLn $ "## wnf_ref_apply        : " ++ show (spine_term_val f) ++ " " ++ show x
  case s of
    FDp0 k l : s' -> do
       wnf_ref_apply e f x s' m (p ++ [(l, D0)])
    FDp1 k l : s' -> do
       wnf_ref_apply e f x s' m (p ++ [(l, D1)])
    _ -> case x of
      FAbs k g -> case s of
        FApp a : s' -> do
          inc_inters e
          let a' = wnf_ref_bind a p
          let m' = IM.insert k a' m
          let f' = spine_add_arg f (Var k)
          wnf_ref_apply e f' g s' m' p
        _ -> wnf_ref_stuck e f s m p

      FSwi z sc -> case s of
        FApp t : s' -> do
          t_val <- case t of
             Zer -> return Zer
             Suc _ -> return t
             Sup _ _ _ -> return t
             Era -> return Era
             _ -> wnf e [] t
          
          case t_val of
            Zer -> do
              inc_inters e
              let f' = spine_add_arg f Zer
              wnf_ref_apply e f' z s' m p
            
            Suc a -> do
              inc_inters e
              let f' = spine_add_suc f
              wnf_ref_apply e f' sc (FApp a : s') m p

            Sup l a b -> do
              inc_inters e
              (s0, s1) <- clone_ref_stack e l s'
              (m0, m1) <- clone_ref_subst e l m
              let p0 = p ++ [(l, D0)]
              let p1 = p ++ [(l, D1)]
              r0 <- wnf_ref_apply e f x (FApp a : s0) m0 p0
              r1 <- wnf_ref_apply e f x (FApp b : s1) m1 p1
              return (Sup l r0 r1)
            
            Era -> return Era

            _ -> wnf_ref_stuck e f s m p

        _ -> wnf_ref_stuck e f s m p

      FFrk k a b -> do
        case lookup_path k p of
          Just D0 -> do
            let p' = remove_path k p
            wnf_ref_apply e f a s m p'
          Just D1 -> do
            let p' = remove_path k p
            wnf_ref_apply e f b s m p'
          Nothing -> do
            (s0, s1) <- clone_ref_stack e k s
            (m0, m1) <- clone_ref_subst e k m
            r0 <- wnf_ref_apply e f a s0 m0 p
            r1 <- wnf_ref_apply e f b s1 m1 p
            return (Sup k r0 r1)

      FDel -> return Era

      FRet t -> do
        t' <- wnf_ref_alloc e t m
        wnf_ref_wrap e t' p

    where
      lookup_path k p = lookup k (reverse p)
      remove_path k p = reverse (remove_one k (reverse p))
      remove_one k [] = []
      remove_one k ((l,d):ps) | k == l = ps | otherwise = (l,d) : remove_one k ps

wnf_ref_stuck :: Env -> Spine -> Stack -> Subs -> Path -> IO Term
wnf_ref_stuck e f s m p = do
  t' <- wnf_ref_alloc e (spine_term_val f) m
  t'' <- wnf_unwind e s t'
  wnf_ref_wrap e t'' p

-- Cloning for Ref Logic
-- ---------------------

clone_ref_stack :: Env -> Lab -> Stack -> IO (Stack, Stack)
clone_ref_stack e l [] = return ([], [])
clone_ref_stack e l (frame : s) = do
  (f0, f1) <- case frame of
    FApp x -> do
      (x0, x1) <- clone e l x
      return (FApp x0, FApp x1)
    FDp0 k l' -> do
      (k0, k1) <- clone_dp_ref e k l
      return (FDp0 k0 l', FDp0 k1 l')
    FDp1 k l' -> do
      (k0, k1) <- clone_dp_ref e k l
      return (FDp1 k0 l', FDp1 k1 l')
  (s0, s1) <- clone_ref_stack e l s
  return (f0 : s0, f1 : s1)

clone_dp_ref :: Env -> Name -> Lab -> IO (Name, Name)
clone_dp_ref e k l = do
  k0 <- fresh e
  k1 <- fresh e
  subst DP0 e k (Sup l (Dp0 k0) (Dp0 k1))
  subst DP1 e k (Sup l (Dp1 k0) (Dp1 k1))
  return (k0, k1)

clone_ref_subst :: Env -> Lab -> Subs -> IO (Subs, Subs)
clone_ref_subst e l m = do
  fmap unzipIntMap $ mapIntMapM (clone e l) m

unzipIntMap :: IM.IntMap (a, b) -> (IM.IntMap a, IM.IntMap b)
unzipIntMap m = (IM.map fst m, IM.map snd m)

mapIntMapM :: Monad m => (a -> m b) -> IM.IntMap a -> m (IM.IntMap b)
mapIntMapM f m = fmap IM.fromList $ mapM (\(k,v) -> fmap ((,) k) (f v)) $ IM.toList m

-- Alloc / Bind / Wrap
-- -------------------

wnf_ref_bind :: Term -> Path -> Term
wnf_ref_bind x [] = x
wnf_ref_bind x ((l, D0):p) = Sup l (wnf_ref_bind x p) Era
wnf_ref_bind x ((l, D1):p) = Sup l Era (wnf_ref_bind x p)

wnf_ref_wrap :: Env -> Term -> Path -> IO Term
wnf_ref_wrap e t [] = return t
wnf_ref_wrap e t ((l, d):p) = do
  k <- fresh e
  t' <- wnf_ref_wrap e t p
  case d of
    D0 -> return $ Dup k l t' (Dp0 k)
    D1 -> return $ Dup k l t' (Dp1 k)

wnf_ref_alloc :: Env -> Term -> Subs -> IO Term
wnf_ref_alloc e term m = go m term where
  go m (Var k) = case IM.lookup k m of
    Just v  -> return v
    Nothing -> return (Var k)
  go m (Dp0 k)       = return (Dp0 k)
  go m (Dp1 k)       = return (Dp1 k)
  go m Era           = return Era
  go m (Sup l a b)   = Sup l <$> go m a <*> go m b
  go m (Dup k l v t) = error "Dup in Book Term not supported in new Ref logic"
  go m Set           = return Set
  go m (All a b)     = All <$> go m a <*> go m b
  go m (Lam k f)     = do
    k' <- fresh e
    f' <- go (IM.insert k (Var k') m) f
    return (Lam k' f')
  go m (App f x)     = App <$> go m f <*> go m x
  go m Nat           = return Nat
  go m Zer           = return Zer
  go m (Suc n)       = Suc <$> go m n
  go m (Ref k)       = return (Ref k)
  go m (Nam k)       = return (Nam k)
  go m (Dry f x)     = Dry <$> go m f <*> go m x

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
    App f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ App f' x'
    Nat -> return Nat
    Zer -> return Zer
    Suc p -> do
      p' <- snf e d p
      return $ Suc p'
    Ref k -> return $ Ref k
    Nam k -> return $ Nam k
    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'

-- Collapsing
-- ==========

col :: Env -> Term -> IO Term
col e x = do
  !x <- wnf e [] x
  case x of
    Era -> return Era
    (Sup l a b) -> do
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
    (Lam k f) -> do
      fV <- fresh e
      f' <- col e f
      inj e (Lam fV (Lam k (Var fV))) [f']
    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- col e f
      x' <- col e x
      inj e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Nat -> return Nat
    Zer -> return Zer
    (Suc p) -> do
      pV <- fresh e
      p' <- col e p
      inj e (Lam pV (Suc (Var pV))) [p']
    Nam n -> return $ Nam n
    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- col e f
      x' <- col e x
      inj e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    x -> return x

inj :: Env -> Term -> [Term] -> IO Term
inj e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    (Sup l a b) -> do
      (f0  , f1 ) <- clone  e l f
      (xs0 , xs1) <- clones e l xs
      a' <- inj e f0 (a : xs0)
      b' <- inj e f1 (b : xs1)
      return $ Sup l a' b'
    x' -> inj e (App f x') xs
inj e f [] = return f

-- Allocation (Standard)
-- =====================

alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where
  go m (Var k)       = return $ Var (IM.findWithDefault k k m)
  go m (Dp0 k)       = return $ Dp0 (IM.findWithDefault k k m)
  go m (Dp1 k)       = return $ Dp1 (IM.findWithDefault k k m)
  go m Era           = return Era
  go m (Sup l a b)   = Sup l <$> go m a <*> go m b
  go m (Dup k l v t) = do
    k' <- fresh e
    v' <- go m v
    t' <- go (IM.insert k k' m) t
    return $ Dup k' l v' t'
  go m Set           = return Set
  go m (All a b)     = All <$> go m a <*> go m b
  go m (Lam k f)     = do
    k' <- fresh e
    f' <- go (IM.insert k k' m) f
    return $ Lam k' f'
  go m (App f x)     = App <$> go m f <*> go m x
  go m Nat           = return Nat
  go m Zer           = return Zer
  go m (Suc n)       = Suc <$> go m n
  go m (Ref k)       = return $ Ref k
  go m (Nam k)       = return $ Nam k
  go m (Dry f x)     = Dry <$> go m f <*> go m x

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
  -- , ("(@not 0)", "1")
  -- , ("(@not 1+0)", "0")
  -- , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  -- , ("(@and 0 0)", "0")
  -- , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  -- , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  -- , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  -- , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(@and 0 a)")
  -- , ("λx.(@and x 0)", "λa.(@and a 0)")
  -- , ("(@sum 1+1+1+0)", "6")
  -- , ("λx.(@sum 1+1+1+x)", "λa.3+(@add a 2+(@add a 1+(@add a (@sum a))))")
  -- , ("(@foo 0)", "&L{0,0}")
  -- , ("(@foo 1+1+1+0)", "&L{3,2}")
  -- , ("λx.(@dbl 1+1+x)", "λa.4+(@dbl a)")
  -- , ("("++f 2++" λX.(X λT0.λF0.F0 λT1.λF1.T1) λT2.λF2.T2)", "λa.λb.a")
  -- , ("1+&L{0,1}", "&L{1,2}")
  -- , ("1+&A{&B{0,1},&C{2,3}}", "&A{&B{1,2},&C{3,4}}")
  -- , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  -- , ("λa.λb.!A&L=a;!B&L=b;&L{λx.(x A₀ B₀),λx.(x A₁ B₁)}", "&L{λa.λb.λc.(c a b),λa.λb.λc.(c a b)}")
  -- , ("λt.(t &A{1,2} 3)", "&A{λa.(a 1 3),λa.(a 2 3)}")
  -- , ("λt.(t 1 &B{3,4})", "&B{λa.(a 1 3),λa.(a 1 4)}")
  -- , ("λt.(t &A{1,2} &A{3,4})", "&A{λa.(a 1 3),λa.(a 2 4)}")
  -- , ("λt.(t &A{1,2} &B{3,4})", "&A{&B{λa.(a 1 3),λa.(a 1 4)},&B{λa.(a 2 3),λa.(a 2 4)}}")
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
  !val <- alloc env $ read_term term_src
  !val <- col env val
  !val <- snf env 1 val
  !end <- getCPUTime
  !itr <- readIORef (env_inters env)
  !dt  <- return $ fromIntegral (end - ini) / (10^12)
  !ips <- return $ fromIntegral itr / dt
  putStrLn $ show val
  putStrLn $ "- Itrs: " ++ show itr ++ " interactions"
  printf "- Time: %.3f seconds\n" (dt :: Double)
  printf "- Perf: %.2f M interactions/s\n" (ips / 1000000 :: Double)

test :: IO ()
test = forM_ tests $ \ (src, exp) -> do
  env <- new_env $ read_book book
  det <- col env $ read_term src
  det <- show <$> snf env 1 det
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " -> " ++ det
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = test









