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
  | Cop !Int !Name
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
  show (Cop s k)     = int_to_name k ++ (if s == 0 then "₀" else "₁")
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
    [ string "₀" >> return (Cop 0 kid)
    , string "₁" >> return (Cop 1 kid)
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

take_sub :: Env -> Name -> IO (Maybe Term)
take_sub e k = taker (env_sub_map e) k

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

make_auto_dup :: Env -> Name -> Lab -> Term -> IO ()
make_auto_dup e k l v = do
  k <- fresh e
  make_dup e k l v

subst :: Env -> Name -> Term -> IO ()
subst e k v = modifyIORef' (env_sub_map e) (IM.insert k v)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Cop 0 k , Cop 1 k)

-- WNF: Weak Normal Form
-- =====================

type WnfDup    = Int -> Env -> Name -> Lab -> Term -> IO Term
type WnfEql    = Env -> Term -> Term -> IO Term
type WnfGuaSwi = Env -> Term -> Term -> Term -> Term -> IO Term

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
            Set   -> wnf_dup_set s e k l v
            All{} -> wnf_dup_all s e k l v
            Lam{} -> wnf_dup_lam s e k l v
            Nat   -> wnf_dup_nat s e k l v
            Zer   -> wnf_dup_zer s e k l v
            Suc{} -> wnf_dup_suc s e k l v
            Swi{} -> wnf_dup_swi s e k l v
            Nam{} -> wnf_dup_nam s e k l v
            Dry{} -> wnf_dup_dry s e k l v
            Gua{} -> wnf_dup_gua s e k l v
            Sig{} -> wnf_dup_sig s e k l v
            Tup{} -> wnf_dup_tup s e k l v
            Get{} -> wnf_dup_get s e k l v
            Emp   -> wnf_dup_emp s e k l v
            Efq   -> wnf_dup_efq s e k l v
            Uni   -> wnf_dup_uni s e k l v
            One   -> wnf_dup_one s e k l v
            Use{} -> wnf_dup_use s e k l v
            Bol   -> wnf_dup_bol s e k l v
            Fal   -> wnf_dup_fal s e k l v
            Tru   -> wnf_dup_tru s e k l v
            If{}  -> wnf_dup_if  s e k l v
            Lst{} -> wnf_dup_lst s e k l v
            Nil   -> wnf_dup_nil s e k l v
            Con{} -> wnf_dup_con s e k l v
            Mat{} -> wnf_dup_mat s e k l v
            _     -> return (Dup k l v (Cop s k))
        Nothing     -> do
          wnf_cop s e k
    App f x -> do
      f <- wnf e f
      case f of
        Era     -> wnf_app_era e f x
        Sup{}   -> wnf_app_sup e f x
        Lam{}   -> wnf_app_lam e f x
        Nam{}   -> wnf_app_nam e f x
        Dry{}   -> wnf_app_dry e f x
        Swi z s -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_swi_era e f x
            Sup{} -> wnf_app_swi_sup e f x
            Zer   -> wnf_app_swi_zer e f x
            Suc{} -> wnf_app_swi_suc e f x
            _     -> return (App f x)
        Get c   -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_get_era e f x
            Sup{} -> wnf_app_get_sup e f x
            Tup{} -> wnf_app_get_tup e f x
            _     -> return (App f x)
        Efq     -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_efq_era e f x
            Sup{} -> wnf_app_efq_sup e f x
            _     -> return (App f x)
        Use u   -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_use_era e f x
            Sup{} -> wnf_app_use_sup e f x
            One   -> wnf_app_use_one e f x
            _     -> return (App f x)
        If ft ff -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_if_era e f x
            Sup{} -> wnf_app_if_sup e f x
            Fal   -> wnf_app_if_fal e f x
            Tru   -> wnf_app_if_tru e f x
            _     -> return (App f x)
        Mat n c  -> do
          x <- wnf e x
          case x of
            Era   -> wnf_app_mat_era e f x
            Sup{} -> wnf_app_mat_sup e f x
            Nil   -> wnf_app_mat_nil e f x
            Con{} -> wnf_app_mat_con e f x
            _     -> return (App f x)
        Gua f g  -> do
          g <- wnf e g
          case g of
            Era     -> wnf_app_gua_era e f g x
            Sup{}   -> wnf_app_gua_sup e f g x
            Lam{}   -> wnf_app_gua_lam e f g x
            Swi z s -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_swi_era e f z s x
                Sup{} -> wnf_app_gua_swi_sup e f z s x
                Zer   -> wnf_app_gua_swi_zer e f z s x
                Suc{} -> wnf_app_gua_swi_suc e f z s x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App f x)
            Get c   -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_get_era e f c x
                Sup{} -> wnf_app_gua_get_sup e f c x
                Tup{} -> wnf_app_gua_get_tup e f c x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App (Gua f g) x)
            Efq     -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_efq_era e f x
                Sup{} -> wnf_app_gua_efq_sup e f x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App (Gua f g) x)
            Use u   -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_use_era e f u x
                Sup{} -> wnf_app_gua_use_sup e f u x
                One   -> wnf_app_gua_use_one e f u x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App (Gua f g) x)
            If ft ff -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_if_era e f ft ff x
                Sup{} -> wnf_app_gua_if_sup e f ft ff x
                Fal   -> wnf_app_gua_if_fal e f ft ff x
                Tru   -> wnf_app_gua_if_tru e f ft ff x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App (Gua f g) x)
            Mat n c  -> do
              x <- wnf e x
              case x of
                Era   -> wnf_app_gua_mat_era e f n c x
                Sup{} -> wnf_app_gua_mat_sup e f n c x
                Nil   -> wnf_app_gua_mat_nil e f n c x
                Con{} -> wnf_app_gua_mat_con e f n c x
                Gua{} -> wnf_app_gua_gua e f g x
                _     -> return (App (Gua f g) x)
            Gua{}    -> wnf_app_gua_gua e f g x
            _        -> return (App (Gua f g) x)
        _       -> return (App f x)
    And a b -> do
      a <- wnf e a
      case a of
        Era   -> wnf_and_era e a b
        Sup{} -> wnf_and_sup e a b
        Fal   -> wnf_and_fal e a b
        Tru   -> wnf_and_tru e a b
        _     -> return (And a b)
    Eql a b -> do
      a <- wnf e a
      case a of
        Era   -> wnf_eql_era e a b
        Sup{} -> wnf_eql_sup e a b
        _     -> do
          b <- wnf e b
          case b of
            Era   -> wnf_eql_val_era e a b
            Sup{} -> wnf_eql_val_sup e a b
            _     -> case (a, b) of
              (Set    , Set)     -> wnf_eql_set_set e a b
              (All{}  , All{})   -> wnf_eql_all_all e a b
              (Lam{}  , Lam{})   -> wnf_eql_lam_lam e a b
              (Sig{}  , Sig{})   -> wnf_eql_sig_sig e a b
              (Tup{}  , Tup{})   -> wnf_eql_tup_tup e a b
              (Get{}  , Get{})   -> wnf_eql_get_get e a b
              (Emp    , Emp)     -> wnf_eql_emp_emp e a b
              (Efq    , Efq)     -> wnf_eql_efq_efq e a b
              (Uni    , Uni)     -> wnf_eql_uni_uni e a b
              (One    , One)     -> wnf_eql_one_one e a b
              (Use{}  , Use{})   -> wnf_eql_use_use e a b
              (Bol    , Bol)     -> wnf_eql_bol_bol e a b
              (Fal    , Fal)     -> wnf_eql_fal_fal e a b
              (Tru    , Tru)     -> wnf_eql_tru_tru e a b
              (Fal    , Tru)     -> wnf_eql_fal_tru e a b
              (Tru    , Fal)     -> wnf_eql_tru_fal e a b
              (If{}   , If{})    -> wnf_eql_if_if e a b
              (Nat    , Nat)     -> wnf_eql_nat_nat e a b
              (Zer    , Zer)     -> wnf_eql_zer_zer e a b
              (Suc{}  , Suc{})   -> wnf_eql_suc_suc e a b
              (Swi{}  , Swi{})   -> wnf_eql_swi_swi e a b
              (Lst{}  , Lst{})   -> wnf_eql_lst_lst e a b
              (Nil    , Nil)     -> wnf_eql_nil_nil e a b
              (Con{}  , Con{})   -> wnf_eql_con_con e a b
              (Mat{}  , Mat{})   -> wnf_eql_mat_mat e a b
              (Nam{}  , Nam{})   -> wnf_eql_nam_nam e a b
              (Dry{}  , Dry{})   -> wnf_eql_dry_dry e a b
              _                  -> wnf_eql_default e a b
    Dup k l v t -> do
      make_dup e k l v
      wnf e t
    Ref k -> do
      wnf_ref e k
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

wnf_dup_0 :: Int -> Env -> Name -> Term -> IO Term
wnf_dup_0 i e k v = do
  inc_inters e
  if i == 0 then do
    subst e k v
    wnf e v
  else do
    subst e k v
    wnf e v

wnf_dup_1 :: Int -> Env -> Name -> Lab -> Term -> (Term -> Term) -> IO Term
wnf_dup_1 i e k l v1 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  if i == 0 then do
    subst e k (c v1b)
    wnf e (c v1a)
  else do
    subst e k (c v1a)
    wnf e (c v1b)

wnf_dup_2 :: Int -> Env -> Name -> Lab -> Term -> Term -> (Term -> Term -> Term) -> IO Term
wnf_dup_2 i e k l v1 v2 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  (v2a, v2b) <- clone e l v2
  if i == 0 then do
    subst e k (c v1b v2b)
    wnf e (c v1a v2a)
  else do
    subst e k (c v1a v2a)
    wnf e (c v1b v2b)

wnf_dup_era :: WnfDup
wnf_dup_era i e k _ Era = wnf_dup_0 i e k Era

wnf_dup_sup :: WnfDup
wnf_dup_sup i e k l (Sup vl va vb)
  | l == vl = do
      inc_inters e
      if i == 0 then do
        subst e k vb
        wnf e va
      else do
        subst e k va
        wnf e vb
  | otherwise = do
      wnf_dup_2 i e k l va vb (Sup vl)

wnf_dup_set :: WnfDup
wnf_dup_set i e k _ Set = wnf_dup_0 i e k Set

wnf_dup_all :: WnfDup
wnf_dup_all i e k l (All va vb) = wnf_dup_2 i e k l va vb All

wnf_dup_lam :: WnfDup
wnf_dup_lam i e k l (Lam vk vf) = do
  inc_inters e
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

wnf_dup_nat :: WnfDup
wnf_dup_nat i e k _ Nat = wnf_dup_0 i e k Nat

wnf_dup_zer :: WnfDup
wnf_dup_zer i e k _ Zer = wnf_dup_0 i e k Zer

wnf_dup_suc :: WnfDup
wnf_dup_suc i e k l (Suc p) = wnf_dup_1 i e k l p Suc

wnf_dup_swi :: WnfDup
wnf_dup_swi i e k l (Swi vz vs) = wnf_dup_2 i e k l vz vs Swi

wnf_dup_nam :: WnfDup
wnf_dup_nam i e k _ (Nam n) = wnf_dup_0 i e k (Nam n)

wnf_dup_dry :: WnfDup
wnf_dup_dry i e k l (Dry vf vx) = wnf_dup_2 i e k l vf vx Dry

wnf_dup_gua :: WnfDup
wnf_dup_gua i e k l (Gua f g) = wnf_dup_2 i e k l f g Gua

wnf_dup_sig :: WnfDup
wnf_dup_sig i e k l (Sig a b) = wnf_dup_2 i e k l a b Sig

wnf_dup_tup :: WnfDup
wnf_dup_tup i e k l (Tup a b) = wnf_dup_2 i e k l a b Tup

wnf_dup_get :: WnfDup
wnf_dup_get i e k l (Get c) = wnf_dup_1 i e k l c Get

wnf_dup_emp :: WnfDup
wnf_dup_emp i e k _ Emp = wnf_dup_0 i e k Emp

wnf_dup_efq :: WnfDup
wnf_dup_efq i e k _ Efq = wnf_dup_0 i e k Efq

wnf_dup_uni :: WnfDup
wnf_dup_uni i e k _ Uni = wnf_dup_0 i e k Uni

wnf_dup_one :: WnfDup
wnf_dup_one i e k _ One = wnf_dup_0 i e k One

wnf_dup_use :: WnfDup
wnf_dup_use i e k l (Use u) = wnf_dup_1 i e k l u Use

wnf_dup_bol :: WnfDup
wnf_dup_bol i e k _ Bol = wnf_dup_0 i e k Bol

wnf_dup_fal :: WnfDup
wnf_dup_fal i e k _ Fal = wnf_dup_0 i e k Fal

wnf_dup_tru :: WnfDup
wnf_dup_tru i e k _ Tru = wnf_dup_0 i e k Tru

wnf_dup_if :: WnfDup
wnf_dup_if i e k l (If f tr) = wnf_dup_2 i e k l f tr If

wnf_dup_lst :: WnfDup
wnf_dup_lst i e k l (Lst x) = wnf_dup_1 i e k l x Lst

wnf_dup_nil :: WnfDup
wnf_dup_nil i e k _ Nil = wnf_dup_0 i e k Nil

wnf_dup_con :: WnfDup
wnf_dup_con i e k l (Con h tr) = wnf_dup_2 i e k l h tr Con

wnf_dup_mat :: WnfDup
wnf_dup_mat i e k l (Mat n c) = wnf_dup_2 i e k l n c Mat

wnf_app_era :: Env -> Term -> Term -> IO Term
wnf_app_era e Era v = do
  inc_inters e
  wnf e Era

wnf_app_nam :: Env -> Term -> Term -> IO Term
wnf_app_nam e (Nam fk) v = wnf e (Dry (Nam fk) v)

wnf_app_dry :: Env -> Term -> Term -> IO Term
wnf_app_dry e (Dry ff fx) v = wnf e (Dry (Dry ff fx) v)

wnf_app_lam :: Env -> Term -> Term -> IO Term
wnf_app_lam e (Lam fx ff) v = do
  inc_inters e
  subst e fx v
  wnf e ff

wnf_app_sup :: Env -> Term -> Term -> IO Term
wnf_app_sup e (Sup fL fa fb) v = do
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e (Sup fL (App fa x0) (App fb x1))

wnf_app_swi_era :: Env -> Term -> Term -> IO Term
wnf_app_swi_era e (Swi z sc) Era = do
  inc_inters e
  wnf e Era

wnf_app_swi_sup :: Env -> Term -> Term -> IO Term
wnf_app_swi_sup e (Swi z sc) (Sup l a b) = do
  inc_inters e
  (z0, z1) <- clone e l z
  (s0, s1) <- clone e l sc
  let app0 = App (Swi z0 s0) a
  let app1 = App (Swi z1 s1) b
  wnf e (Sup l app0 app1)

wnf_app_swi_zer :: Env -> Term -> Term -> IO Term
wnf_app_swi_zer e (Swi z sc) Zer = do
  inc_inters e
  wnf e z

wnf_app_swi_suc :: Env -> Term -> Term -> IO Term
wnf_app_swi_suc e (Swi z sc) (Suc n) = do
  inc_inters e
  wnf e (App sc n)

wnf_app_get_era :: Env -> Term -> Term -> IO Term
wnf_app_get_era e f Era = do
  inc_inters e
  wnf e Era

wnf_app_get_sup :: Env -> Term -> Term -> IO Term
wnf_app_get_sup e (Get c) (Sup l x y) = do
  inc_inters e
  (c0, c1) <- clone e l c
  wnf e (Sup l (App (Get c0) x) (App (Get c1) y))

wnf_app_get_tup :: Env -> Term -> Term -> IO Term
wnf_app_get_tup e (Get c) (Tup x y) = do
  inc_inters e
  wnf e (App (App c x) y)

wnf_app_efq_era :: Env -> Term -> Term -> IO Term
wnf_app_efq_era e f Era = do
  inc_inters e
  wnf e Era

wnf_app_efq_sup :: Env -> Term -> Term -> IO Term
wnf_app_efq_sup e Efq (Sup l x y) = do
  inc_inters e
  wnf e (Sup l (App Efq x) (App Efq y))

wnf_app_use_era :: Env -> Term -> Term -> IO Term
wnf_app_use_era e f Era = do
  inc_inters e
  wnf e Era

wnf_app_use_sup :: Env -> Term -> Term -> IO Term
wnf_app_use_sup e (Use u) (Sup l x y) = do
  inc_inters e
  (u0, u1) <- clone e l u
  wnf e (Sup l (App (Use u0) x) (App (Use u1) y))

wnf_app_use_one :: Env -> Term -> Term -> IO Term
wnf_app_use_one e (Use u) One = do
  inc_inters e
  wnf e u

wnf_app_if_era :: Env -> Term -> Term -> IO Term
wnf_app_if_era e f Era = do
  inc_inters e
  wnf e Era

wnf_app_if_sup :: Env -> Term -> Term -> IO Term
wnf_app_if_sup e (If ft ff) (Sup l x y) = do
  inc_inters e
  (ft0, ft1) <- clone e l ft
  (ff0, ff1) <- clone e l ff
  wnf e (Sup l (App (If ft0 ff0) x) (App (If ft1 ff1) y))

wnf_app_if_fal :: Env -> Term -> Term -> IO Term
wnf_app_if_fal e (If ft ff) Fal = do
  inc_inters e
  wnf e ft

wnf_app_if_tru :: Env -> Term -> Term -> IO Term
wnf_app_if_tru e (If ft ff) Tru = do
  inc_inters e
  wnf e ff

wnf_app_mat_era :: Env -> Term -> Term -> IO Term
wnf_app_mat_era e f Era = do
  inc_inters e
  wnf e Era

wnf_app_mat_sup :: Env -> Term -> Term -> IO Term
wnf_app_mat_sup e (Mat n c) (Sup l x y) = do
  inc_inters e
  (n0, n1) <- clone e l n
  (c0, c1) <- clone e l c
  wnf e (Sup l (App (Mat n0 c0) x) (App (Mat n1 c1) y))

wnf_app_mat_nil :: Env -> Term -> Term -> IO Term
wnf_app_mat_nil e (Mat n c) Nil = do
  inc_inters e
  wnf e n

wnf_app_mat_con :: Env -> Term -> Term -> IO Term
wnf_app_mat_con e (Mat n c) (Con h t) = do
  inc_inters e
  wnf e (App (App c h) t)

wnf_app_gua_era :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_era e f Era a = do
  inc_inters e
  wnf e Era

wnf_app_gua_sup :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_sup e f (Sup l x y) a = do
  inc_inters e
  (f0,f1) <- clone e l f
  (a0,a1) <- clone e l a
  let app0 = (App (Gua f0 x) a0)
  let app1 = (App (Gua f1 y) a1)
  wnf e (Sup l app0 app1)

wnf_app_gua_lam :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_lam e f (Lam x g) a = do
  inc_inters e
  subst e x a
  wnf e (Gua (App f (Var x)) g)

wnf_app_gua_gua :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_gua e f g a = do
  inc_inters e
  wnf e (Gua (App f a) (App g a))

wnf_app_gua_swi_era :: WnfGuaSwi
wnf_app_gua_swi_era e f z sc Era = do
  wnf e Era

wnf_app_gua_swi_sup :: WnfGuaSwi
wnf_app_gua_swi_sup e f z sc (Sup l a b) = do
  inc_inters e
  (f0,f1) <- clone e l f
  (z0,z1) <- clone e l z
  (s0,s1) <- clone e l sc
  let app0 = App (Gua f0 (Swi z0 s0)) a
  let app1 = App (Gua f1 (Swi z1 s1)) b
  wnf e (Sup l app0 app1)

wnf_app_gua_swi_zer :: WnfGuaSwi
wnf_app_gua_swi_zer e f z sc Zer = do
  inc_inters e
  wnf e (Gua (App f Zer) z)

wnf_app_gua_swi_suc :: WnfGuaSwi
wnf_app_gua_swi_suc e f z sc (Suc n) = do
  inc_inters e
  p <- fresh e
  let fn = (Lam p (App f (Suc (Var p))))
  wnf e (App (Gua fn sc) n)

wnf_app_gua_get_era :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_get_era e f c a = do
  inc_inters e
  wnf e Era

wnf_app_gua_get_sup :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_get_sup e f c (Sup l x y) = do
  inc_inters e
  (f0, f1) <- clone e l f
  (c0, c1) <- clone e l c
  wnf e (Sup l (App (Gua f0 (Get c0)) x) (App (Gua f1 (Get c1)) y))

wnf_app_gua_get_tup :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_get_tup e f c (Tup x y) = do
  inc_inters e
  xV <- fresh e
  yV <- fresh e
  let fn = Lam xV (Lam yV (App f (Tup (Var xV) (Var yV))))
  wnf e (App (App (Gua fn c) x) y)

wnf_app_gua_efq_era :: Env -> Term -> Term -> IO Term
wnf_app_gua_efq_era e f a = do
  inc_inters e
  wnf e Era

wnf_app_gua_efq_sup :: Env -> Term -> Term -> IO Term
wnf_app_gua_efq_sup e f (Sup l x y) = do
  inc_inters e
  (f0, f1) <- clone e l f
  wnf e (Sup l (App (Gua f0 Efq) x) (App (Gua f1 Efq) y))

wnf_app_gua_use_era :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_use_era e f u a = do
  inc_inters e
  wnf e Era

wnf_app_gua_use_sup :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_use_sup e f u (Sup l x y) = do
  inc_inters e
  (f0, f1) <- clone e l f
  (u0, u1) <- clone e l u
  wnf e (Sup l (App (Gua f0 (Use u0)) x) (App (Gua f1 (Use u1)) y))

wnf_app_gua_use_one :: Env -> Term -> Term -> Term -> IO Term
wnf_app_gua_use_one e f u One = do
  inc_inters e
  wnf e (Gua (App f One) u)

wnf_app_gua_if_era :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_if_era e f ft ff a = do
  inc_inters e
  wnf e Era

wnf_app_gua_if_sup :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_if_sup e f ft ff (Sup l x y) = do
  inc_inters e
  (f0, f1) <- clone e l f
  (ft0, ft1) <- clone e l ft
  (ff0, ff1) <- clone e l ff
  wnf e (Sup l (App (Gua f0 (If ft0 ff0)) x) (App (Gua f1 (If ft1 ff1)) y))

wnf_app_gua_if_fal :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_if_fal e f ft ff Fal = do
  inc_inters e
  wnf e (Gua (App f Fal) ft)

wnf_app_gua_if_tru :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_if_tru e f ft ff Tru = do
  inc_inters e
  wnf e (Gua (App f Tru) ff)

wnf_app_gua_mat_era :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat_era e f n c a = do
  inc_inters e
  wnf e Era

wnf_app_gua_mat_sup :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat_sup e f n c (Sup l x y) = do
  inc_inters e
  (f0, f1) <- clone e l f
  (n0, n1) <- clone e l n
  (c0, c1) <- clone e l c
  wnf e (Sup l (App (Gua f0 (Mat n0 c0)) x) (App (Gua f1 (Mat n1 c1)) y))

wnf_app_gua_mat_nil :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat_nil e f n c Nil = do
  inc_inters e
  wnf e (Gua (App f Nil) n)

wnf_app_gua_mat_con :: Env -> Term -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat_con e f n c (Con h t) = do
  inc_inters e
  hV <- fresh e
  tV <- fresh e
  let fn = Lam hV (Lam tV (App f (Con (Var hV) (Var tV))))
  wnf e (App (App (Gua fn c) h) t)

wnf_and_era :: Env -> Term -> Term -> IO Term
wnf_and_era e Era b = do
  inc_inters e
  wnf e Era

wnf_and_sup :: Env -> Term -> Term -> IO Term
wnf_and_sup e (Sup l a0 a1) b = do
  inc_inters e
  (b0, b1) <- clone e l b
  wnf e (Sup l (And a0 b0) (And a1 b1))

wnf_and_fal :: Env -> Term -> Term -> IO Term
wnf_and_fal e Fal b = do
  inc_inters e
  wnf e Fal

wnf_and_tru :: Env -> Term -> Term -> IO Term
wnf_and_tru e Tru b = do
  inc_inters e
  wnf e b

wnf_eql_era :: Env -> Term -> Term -> IO Term
wnf_eql_era e Era b = do
  inc_inters e
  wnf e Era

wnf_eql_sup :: Env -> Term -> Term -> IO Term
wnf_eql_sup e (Sup l a0 a1) b = do
  inc_inters e
  k <- fresh e
  make_dup e k l b
  wnf e (Sup l (Eql a0 (Cop 0 k)) (Eql a1 (Cop 1 k)))

wnf_eql_val_era :: Env -> Term -> Term -> IO Term
wnf_eql_val_era e a Era = do
  inc_inters e
  wnf e Era

wnf_eql_val_sup :: Env -> Term -> Term -> IO Term
wnf_eql_val_sup e a (Sup l b0 b1) = do
  inc_inters e
  k <- fresh e
  make_dup e k l a
  wnf e (Sup l (Eql (Cop 0 k) b0) (Eql (Cop 1 k) b1))

wnf_eql_set_set :: WnfEql
wnf_eql_set_set e Set Set = do
  inc_inters e
  wnf e Tru

wnf_eql_all_all :: WnfEql
wnf_eql_all_all e (All aA aB) (All bA bB) = do
  inc_inters e
  wnf e (And (Eql aA bA) (Eql aB bB))

wnf_eql_lam_lam :: WnfEql
wnf_eql_lam_lam e (Lam ax af) (Lam bx bf) = do
  inc_inters e
  x <- fresh e
  subst e ax (Nam (int_to_name x))
  subst e bx (Nam (int_to_name x))
  wnf e (Eql af bf)

wnf_eql_sig_sig :: WnfEql
wnf_eql_sig_sig e (Sig aA aB) (Sig bA bB) = do
  inc_inters e
  wnf e (And (Eql aA bA) (Eql aB bB))

wnf_eql_tup_tup :: WnfEql
wnf_eql_tup_tup e (Tup a1 a2) (Tup b1 b2) = do
  inc_inters e
  wnf e (And (Eql a1 b1) (Eql a2 b2))

wnf_eql_get_get :: WnfEql
wnf_eql_get_get e (Get ac) (Get bc) = do
  inc_inters e
  wnf e (Eql ac bc)

wnf_eql_emp_emp :: WnfEql
wnf_eql_emp_emp e Emp Emp = do
  inc_inters e
  wnf e Tru

wnf_eql_efq_efq :: WnfEql
wnf_eql_efq_efq e Efq Efq = do
  inc_inters e
  wnf e Tru

wnf_eql_uni_uni :: WnfEql
wnf_eql_uni_uni e Uni Uni = do
  inc_inters e
  wnf e Tru

wnf_eql_one_one :: WnfEql
wnf_eql_one_one e One One = do
  inc_inters e
  wnf e Tru

wnf_eql_use_use :: WnfEql
wnf_eql_use_use e (Use au) (Use bu) = do
  inc_inters e
  wnf e (Eql au bu)

wnf_eql_bol_bol :: WnfEql
wnf_eql_bol_bol e Bol Bol = do
  inc_inters e
  wnf e Tru

wnf_eql_fal_fal :: WnfEql
wnf_eql_fal_fal e Fal Fal = do
  inc_inters e
  wnf e Tru

wnf_eql_tru_tru :: WnfEql
wnf_eql_tru_tru e Tru Tru = do
  inc_inters e
  wnf e Tru

wnf_eql_fal_tru :: WnfEql
wnf_eql_fal_tru e Fal Tru = do
  inc_inters e
  wnf e Fal

wnf_eql_tru_fal :: WnfEql
wnf_eql_tru_fal e Tru Fal = do
  inc_inters e
  wnf e Fal

wnf_eql_if_if :: WnfEql
wnf_eql_if_if e (If af at) (If bf bt) = do
  inc_inters e
  wnf e (And (Eql af bf) (Eql at bt))

wnf_eql_nat_nat :: WnfEql
wnf_eql_nat_nat e Nat Nat = do
  inc_inters e
  wnf e Tru

wnf_eql_zer_zer :: WnfEql
wnf_eql_zer_zer e Zer Zer = do
  inc_inters e
  wnf e Tru

wnf_eql_suc_suc :: WnfEql
wnf_eql_suc_suc e (Suc a) (Suc b) = do
  inc_inters e
  wnf e (Eql a b)

wnf_eql_swi_swi :: WnfEql
wnf_eql_swi_swi e (Swi az as) (Swi bz bs) = do
  inc_inters e
  wnf e (And (Eql az bz) (Eql as bs))

wnf_eql_lst_lst :: WnfEql
wnf_eql_lst_lst e (Lst aT) (Lst bT) = do
  inc_inters e
  wnf e (Eql aT bT)

wnf_eql_nil_nil :: WnfEql
wnf_eql_nil_nil e Nil Nil = do
  inc_inters e
  wnf e Tru

wnf_eql_con_con :: WnfEql
wnf_eql_con_con e (Con ah at) (Con bh bt) = do
  inc_inters e
  wnf e (And (Eql ah bh) (Eql at bt))

wnf_eql_mat_mat :: WnfEql
wnf_eql_mat_mat e (Mat an ac) (Mat bn bc) = do
  inc_inters e
  wnf e (And (Eql an bn) (Eql ac bc))

wnf_eql_nam_nam :: WnfEql
wnf_eql_nam_nam e (Nam x) (Nam y) = do
  inc_inters e
  if x == y then
    wnf e Tru
  else
    wnf e Fal

wnf_eql_dry_dry :: WnfEql
wnf_eql_dry_dry e (Dry af ax) (Dry bf bx) = do
  inc_inters e
  wnf e (And (Eql af bf) (Eql ax bx))

wnf_eql_default :: WnfEql
wnf_eql_default e a b = do
  wnf e Fal

wnf_ref :: Env -> Name -> IO Term
wnf_ref e k = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- alloc e f
      wnf e g
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

-- Allocation
-- ==========

-- Allocates a closed term, replacing all bound names with fresh ones.
alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where

  go :: IM.IntMap Name -> Term -> IO Term

  go m (Var k) = do
    return $ Var (IM.findWithDefault k k m)

  go m (Cop s k) = do
    return $ Cop s (IM.findWithDefault k k m)

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
      -- subst 1 e k (Nam (int_to_name d ++ "₀"))
      -- subst 2 e k (Nam (int_to_name d ++ "₁"))
      -- v' <- snf e d v
      -- t' <- snf e d t
      -- return $ Dup d l v' t'

    Set -> do
      return $ Set

    All a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ All a' b'

    Lam k f -> do
      subst e k (Nam (int_to_name d))
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
  !x <- wnf e x
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
  !xs <- wnf e xs
  case xs of
    Era -> do
      error "TODO"
    Sup xsl xsa xsb -> do
      error "TODO"
    Nil -> do
      return $ f
    Con h t -> do
      !h <- wnf e h
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
