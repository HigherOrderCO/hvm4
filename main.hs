-- Calculus of Interactions
-- ========================
-- 
-- CoI is a term rewrite system for the following grammar:
--
-- Term ::=
-- | Var ::= Name
-- | Dp0 ::= Name "₀"
-- | Dp1 ::= Name "₁"
-- | Era ::= "&{}"
-- | Sup ::= "&" Name "{" Term "," Term "}"
-- | Dup ::= "!" Name "&" Name "=" Term ";" Term
-- | Set ::= "*"
-- | All ::= "∀" Term "." Term
-- | Lam ::= "λ" Name "." Term
-- | App ::= "(" Term " " Term ")"
-- | Nat ::= "ℕ"
-- | Zer ::= "0"
-- | Suc ::= "1+"
-- | Swi ::= "λ" "{" "0" ":" Term ";"? "1+" ":" Term ";"? "}"
-- | Ref ::= "@" Name
-- | Nam ::= "." Name
-- | Dry ::= "." "(" Term " " Term ")"
-- | Sup ::= "&" Name "{" Term "," Term "}"
--
-- Where:
-- - Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $
-- - [T]  ::= any sequence of T separated by ","
-- 
-- In CoI:
-- - Variables are affine (they must occur at most once)
-- - Variables range globally (they can occur anywhere)
-- 
-- Interaction Table
-- =================
-- 
-- ! X &L = &{}
-- ------------ dup-era
-- X₀ ← &{}
-- X₁ ← &{}
--
-- ! X &L = &R{a,b}
-- ---------------- dup-sup
-- if L == R:
--   X₀ ← a
--   X₁ ← b
-- else:
--   ! A &L = a
--   ! B &L = b
--   X₀ ← &R{A₀,B₀}
--   X₁ ← &R{A₁,B₁}
--
-- ! X &L = *
-- ---------- dup-set
-- X₀ ← *
-- X₁ ← *
--
-- ! X &L = ∀a.b
-- ------------- dup-all
-- ! A &L = a
-- ! B &L = b
-- X₀ ← ∀A₀.B₀
-- X₁ ← ∀A₁.B₁
--
-- ! F &L = λx.f
-- ---------------- dup-lam
-- F₀ ← λ$x0.G₀
-- F₁ ← λ$x1.G₁
-- x  ← &L{$x0,$x1}
-- ! G &L = f
--
-- ! X &L = ℕ
-- ---------- dup-nat
-- X₀ ← ℕ
-- X₁ ← ℕ
--
-- ! X &L = 1+n
-- ------------ dup-suc
-- ! N &L = n
-- X₀ ← 1+N₀
-- X₁ ← 1+N₁
--
-- ! X &L = 0
-- ---------- dup-zer
-- X₀ ← 0
-- X₁ ← 0
--
-- ! X &L = .n
-- ----------- dup-nam
-- X₀ ← .n
-- X₁ ← .n
--
-- ! X &L = .(f x)
-- --------------- dup-dry
-- ! F &L = f
-- ! A &L = x
-- X₀ ← .(F₀ A₀)
-- X₁ ← .(F₁ A₁)
--
-- (&{} a)
-- ------- app-era
-- &{}
--
-- (&L{f,g} a)
-- ----------------- app-sup
-- ! A &L = a
-- &L{(f A₀),(g A₁)}
--
-- (λx.f a)
-- -------- app-lam
-- x ← a
-- f
--
-- (.n a)
-- ------ app-nam
-- .(.n a)
--
-- (.(f x) a)
-- ---------- app-dry
-- .(.(f x) a)
--
-- Function Call
-- =============
-- 
-- A state (F, X, S, M, P) is evolved, where:
-- - F: Spine = current call context
-- - X: Term  = current Term from book
-- - S: Stack = argument stack
-- - M: Map   = static substitutions
-- - P: Path  = dup label path
--
-- (F, λx.G, (_ A):S, M, P)
-- -------------------------------- ref-app-lam
-- (F(x), G, S, {x→bind(A,P)|M}, P)
--
-- (F, λ{0:Z;1+:S}, 0:S, M, P)
-- --------------------------- ref-app-swi-zer
-- (F(0), Z, S, M, P)
--
-- (F, λ{0:Z;1+:S}, 1+A:S, M, P)
-- ----------------------------- ref-app-swi-suc
-- (\h->F(1+h), S, A:S, M, P)
--
-- (F, λ{0:Z;1+:S}, &L{A,B}:S, M, P)
-- --------------------------------- ref-app-swi-sup
-- &L{
--   (F, λ{0:Z;1+:S}, A:S, M, P++[&L₀])
--   (F, λ{0:Z;1+:S}, B:S, M, P++[&L₁])
-- }
--
-- (F, G, (!K&L=_; K₀):S, M, P)
-- ---------------------------- ref-dup-0
-- (F, G, S, M, P++[&L₀])
--
-- (F, G, (!K&L=_; K₁):S, M, P)
-- ---------------------------- ref-dup-1
-- (F, G, S, M, P++[&L₁])
--
-- (F, &{}, S, M, P)
-- ----------------- ref-del
-- &{}
--
-- (F, &L{X,Y}, S, M, P)
-- --------------------- ref-sup
-- if &L₀ ∈ P:
--   (F, X, S, M, P - {&L})
-- else if &L₁ ∈ P:
--   (F, Y, S, M, P - {&L})
-- else:
--   ! F &L = F
--   ! S &L = S
--   ! M &L = M
--   &L{
--     (F₀, X, S₀, M₀, P)
--     (F₁, Y, S₁, M₁, P)
--   }
--
-- (F, G, S, M, P)
-- -------------------- ref-alloc
-- if complete:
--   wrap(alloc(G, M), P)
-- else:
--   wrap(alloc(F, M), P)

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
  | Swi !Term !Term
  | App !Term !Term
  | Nat
  | Zer
  | Suc !Term
  | Ref !Name
  | Nam !String
  | Dry !Term !Term
  deriving (Eq)

data Book = Book (M.Map Name Term)
type Path = [(Lab, Int)]
type Subs = IM.IntMap Term
data Semi = Semi !Int !([Term] -> Term)

data Env = Env
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_sub_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

instance Show Semi where
  show sp = show (semi_term sp)

data Frame
  = FApp !Term
  | FDp0 !Name !Lab
  | FDp1 !Name !Lab
  deriving (Show)

type Stack = [Frame]

-- Utils
-- =====

name_of :: Term -> Name
name_of (Var k) = k
name_of (Dp0 k) = k
name_of (Dp1 k) = k

dp :: Int -> Name -> Term
dp 0 k = Dp0 k
dp 1 k = Dp1 k

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
  show (Swi z s)     = "λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
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
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

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
  [ parse_swi
  , parse_lam
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

parse_swi :: ReadP Term
parse_swi = do
  lexeme (char 'λ')
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "0:")
    z <- parse_term
    optional (lexeme (char ';'))
    lexeme (string "1+:")
    s <- parse_term
    return (Swi z s)

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

parse_book_entry :: ReadP (Name, Term)
parse_book_entry = do
  lexeme (char '@')
  k <- parse_nam
  lexeme (char '=')
  f <- parse_term
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

map_take :: IORef (IM.IntMap a) -> Int -> IO (Maybe a)
map_take ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = map_take (env_dup_map e) k

take_sub :: Env -> Name -> IO (Maybe Term)
take_sub e k = map_take (env_sub_map e) k

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

subst :: Env -> Name -> Term -> IO ()
subst e k v = modifyIORef' (env_sub_map e) (IM.insert k v)

-- Cloning
-- -------

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return (Dp0 k, Dp1 k)

clones :: Env -> Lab -> [Term] -> IO ([Term],[Term])
clones _ _ []       = return ([],[])
clones e l (x : xs) = do
  (x0  , x1 ) <- clone  e l x
  (xs0 , xs1) <- clones e l xs
  return (x0 : xs0 , x1 : xs1)

clone2 :: Env -> Lab -> (Term,Term) -> IO ((Term,Term),(Term,Term))
clone2 e l (x,y) = do
  (x0,x1) <- clone e l x
  (y0,y1) <- clone e l y
  return ((x0,y0),(x1,y1))

clone2s :: Env -> Lab -> [(Term,Term)] -> IO ([(Term,Term)],[(Term,Term)])
clone2s e l []         = return $ ([],[])
clone2s e l (xy : xys) = do
  (xy0  , xy1 ) <- clone2  e l xy
  (xys0 , xys1) <- clone2s e l xys
  return $ (xy0 : xys0, xy1 : xys1)

clone_ref_stack :: Env -> Lab -> Stack -> IO (Stack, Stack)
clone_ref_stack _ _ [] = do
  return ([], [])
clone_ref_stack e l (frame : s) = do
  (f0, f1) <- case frame of
    FApp x -> do
      (x0, x1) <- clone e l x
      return (FApp x0, FApp x1)
    FDp0 k l' -> do
      (k0, k1) <- clone_ref_stack_dup 0 e k l
      return (FDp0 k0 l', FDp0 k1 l')
    FDp1 k l' -> do
      (k0, k1) <- clone_ref_stack_dup 1 e k l
      return (FDp1 k0 l', FDp1 k1 l')
  (s0, s1) <- clone_ref_stack e l s
  return (f0 : s0, f1 : s1)

clone_ref_stack_dup :: Int -> Env -> Name -> Lab -> IO (Name, Name)
clone_ref_stack_dup d e k l = do
  k0 <- fresh e
  k1 <- fresh e
  if d == 0 then do
    subst e k (Sup l (Dp1 k0) (Dp1 k1))
  else do
    subst e k (Sup l (Dp0 k0) (Dp0 k1))
  return (k0, k1)

clone_ref_subst :: Env -> Lab -> Subs -> IO (Subs, Subs)
clone_ref_subst e l m = go (IM.toList m) IM.empty IM.empty where
  go []            m0 m1 = return (m0, m1)
  go ((k,v):rest)  m0 m1 = do
    (v0, v1) <- clone e l v
    go rest (IM.insert k v0 m0) (IM.insert k v1 m1)

-- Semi
-- =====

semi_new :: Name -> Semi
semi_new k = Semi 0 (\_ -> Nam ("@" ++ (int_to_name k)))

semi_app :: Semi -> Term -> Semi
semi_app (Semi n f) x = Semi n (\hs -> App (f hs) x)

semi_ctr :: Semi -> Semi
semi_ctr (Semi n f) = Semi (n + 1) (\ (h:hs) -> App (f hs) (Suc h))

semi_term :: Semi -> Term
semi_term (Semi n f) = f (replicate n (Nam "_"))

-- WNF: Weak Normal Form
-- =====================

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

-- WNF: Enter
-- ----------

wnf_enter :: Env -> Stack -> Term -> IO Term

wnf_enter e s (Var k) = do
  when debug $ putStrLn $ ">> wnf_enter_var        : " ++ show (Var k)
  wnf_sub e s (Var k)

wnf_enter e s (Dp0 k) = do
  when debug $ putStrLn $ ">> wnf_enter_dp0        : " ++ show (Dp0 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub e s (Dp0 k)

wnf_enter e s (Dp1 k) = do
  when debug $ putStrLn $ ">> wnf_enter_dp1        : " ++ show (Dp1 k)
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub e s (Dp1 k)

wnf_enter e s (App f x) = do
  when debug $ putStrLn $ ">> wnf_enter_app        : " ++ show (App f x)
  wnf_enter e (FApp x : s) f

wnf_enter e s (Dup k l v t) = do
  when debug $ putStrLn $ ">> wnf_enter_dup        : " ++ show (Dup k l v t)
  make_dup e k l v
  wnf_enter e s t

wnf_enter e s (Ref k) = do
  when debug $ putStrLn $ ">> wnf_enter_ref        : " ++ show (Ref k)
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> wnf_ref_app e (semi_new k) f s IM.empty []
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

wnf_enter e s f = do
  when debug $ putStrLn $ ">> wnf_enter            : " ++ show f
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind _ [] v = return v
wnf_unwind e (fr:s) v = do
  when debug $ putStrLn $ ">> wnf_unwind           : " ++ show v
  case fr of
    FApp x      -> wnf_app e s v x
    FDp0 k l    -> wnd_dup 0 e s k l v
    FDp1 k l    -> wnd_dup 1 e s k l v

wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s v x = case v of
  Era          -> wnf_app_era e s x
  Sup fl fa fb -> wnf_app_sup e s fl fa fb x
  Set          -> wnf_app_set e s x
  All va vb    -> wnf_app_all e s va vb x
  Lam fk ff    -> wnf_app_lam e s fk ff x
  Swi vz vs    -> wnf_app_swi e s vz vs x
  Nat          -> wnf_app_nat e s x
  Zer          -> wnf_app_zer e s x
  Suc vp       -> wnf_app_suc e s vp x
  Nam fk       -> wnf_app_nam e s fk x
  Dry ff fx    -> wnf_app_dry e s ff fx x
  f'           -> wnf_unwind e s (App f' x)

wnd_dup :: Int -> Env -> Stack -> Name -> Lab -> Term -> IO Term
wnd_dup d e s k l v = case v of
  Era          -> wnd_dup_era d e s k l
  Sup vl va vb -> wnd_dup_sup d e s k l vl va vb
  Set          -> wnd_dup_set d e s k l
  All va vb    -> wnd_dup_all d e s k l va vb
  Lam vk vf    -> wnd_dup_lam d e s k l vk vf
  Swi vz vs    -> wnd_dup_swi d e s k l vz vs
  Nat          -> wnd_dup_nat d e s k l
  Zer          -> wnd_dup_zer d e s k l
  Suc vp       -> wnd_dup_suc d e s k l vp
  Nam vk       -> wnd_dup_nam d e s k l vk
  Dry vf vx    -> wnd_dup_dry d e s k l vf vx
  val          -> wnf_unwind e s (Dup k l val (dp d k))

-- WNF: Interactions
-- -----------------

wnf_sub :: Env -> Stack -> Term -> IO Term
wnf_sub e s v = do
  when debug $ putStrLn $ "## wnf_sub              : " ++ int_to_name (name_of v)
  mt <- take_sub e (name_of v)
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s v

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
  subst e fx v
  wnf e s ff

wnf_app_swi :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_swi e s vz vs x = case x of
  Zer          -> wnf_app_swi_zer e s vz vs
  Suc vn       -> wnf_app_swi_suc e s vz vs vn
  Sup xl xa xb -> wnf_app_swi_sup e s vz vs xl xa xb
  _            -> wnf_unwind e s (App (Swi vz vs) x)

wnf_app_swi_zer :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_zer e s vz vs = do
  when debug $ putStrLn $ "## wnf_app_swi_zer      : " ++ show (App (Swi vz vs) Zer)
  inc_inters e
  _ <- wnf_app e [] Era vs
  wnf e s vz

wnf_app_swi_suc :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_swi_suc e s vz vs vn = do
  when debug $ putStrLn $ "## wnf_app_swi_suc      : " ++ show (App (Swi vz vs) (Suc vn))
  inc_inters e
  _ <- wnf_app e [] Era vz
  wnf_app e s vs vn

wnf_app_swi_sup :: Env -> Stack -> Term -> Term -> Lab -> Term -> Term -> IO Term
wnf_app_swi_sup e s vz vs l xa xb = do
  when debug $ putStrLn $ "## wnf_app_swi_sup      : " ++ show (App (Swi vz vs) (Sup l xa xb))
  inc_inters e
  (z0,z1) <- clone e l vz
  (s0,s1) <- clone e l vs
  let sw0 = Swi z0 s0
  let sw1 = Swi z1 s1
  wnf e s (Sup l (App sw0 xa) (App sw1 xb))

wnf_app_sup :: Env -> Stack -> Lab -> Term -> Term -> Term -> IO Term
wnf_app_sup e s fL fa fb v = do
  when debug $ putStrLn $ "## wnf_app_sup          : " ++ show (App (Sup fL fa fb) v)
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

wnd_dup_era :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnd_dup_era d e s k _ = do
  when debug $ putStrLn $ "## wnd_dup_era          : " ++ show (Dup k (name_to_int "_") Era (dp d k))
  inc_inters e
  subst e k Era
  wnf e s Era

wnd_dup_sup :: Int -> Env -> Stack -> Name -> Lab -> Lab -> Term -> Term -> IO Term
wnd_dup_sup d e s k l vl va vb
  | l == vl = do
      when debug $ putStrLn $ "## wnd_dup_sup_same     : " ++ show (Dup k l (Sup vl va vb) (dp d k))
      inc_inters e
      if d == 0 then do
        subst e k vb
        wnf e s va
      else do
        subst e k va
        wnf e s vb
  | otherwise = do
      when debug $ putStrLn $ "## wnd_dup_sup_diff     : " ++ show (Dup k l (Sup vl va vb) (dp d k))
      inc_inters e
      (a0,a1) <- clone e l va
      (b0,b1) <- clone e l vb
      let val0 = Sup vl a0 b0
      let val1 = Sup vl a1 b1
      if d == 0 then do
        subst e k val1
        wnf e s val0
      else do
        subst e k val0
        wnf e s val1

wnd_dup_set :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnd_dup_set d e s k _ = do
  when debug $ putStrLn $ "## wnd_dup_set          : " ++ show (Dup k (name_to_int "_") Set (dp d k))
  inc_inters e
  subst e k Set
  wnf e s Set

wnd_dup_all :: Int -> Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnd_dup_all d e s k l va vb = do
  when debug $ putStrLn $ "## wnd_dup_all          : " ++ show (Dup k l (All va vb) (dp d k))
  inc_inters e
  (a0,a1) <- clone e l va
  (b0,b1) <- clone e l vb
  let val0 = All a0 b0
  let val1 = All a1 b1
  if d == 0 then do
    subst e k val1
    wnf e s val0
  else do
    subst e k val0
    wnf e s val1

wnd_dup_lam :: Int -> Env -> Stack -> Name -> Lab -> Name -> Term -> IO Term
wnd_dup_lam d e s k l vk vf = do
  when debug $ putStrLn $ "## wnd_dup_lam          : " ++ show (Dup k l (Lam vk vf) (dp d k))
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst e vk (Sup l (Var x0) (Var x1))
  let val0 = Lam x0 g0
  let val1 = Lam x1 g1
  if d == 0 then do
    subst e k val1
    wnf e s val0
  else do
    subst e k val0
    wnf e s val1

wnd_dup_swi :: Int -> Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnd_dup_swi d e s k l vz vs = do
  when debug $ putStrLn $ "## wnd_dup_swi          : " ++ show (Dup k l (Swi vz vs) (dp d k))
  inc_inters e
  (z0,z1) <- clone e l vz
  (s0,s1) <- clone e l vs
  let val0 = Swi z0 s0
  let val1 = Swi z1 s1
  if d == 0 then do
    subst e k val1
    wnf e s val0
  else do
    subst e k val0
    wnf e s val1

wnd_dup_nat :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnd_dup_nat d e s k _ = do
  when debug $ putStrLn $ "## wnd_dup_nat          : " ++ show (Dup k (name_to_int "_") Nat (dp d k))
  inc_inters e
  subst e k Nat
  wnf e s Nat

wnd_dup_zer :: Int -> Env -> Stack -> Name -> Lab -> IO Term
wnd_dup_zer d e s k _ = do
  when debug $ putStrLn $ "## wnd_dup_zer          : " ++ show (Dup k (name_to_int "_") Zer (dp d k))
  inc_inters e
  subst e k Zer
  wnf e s Zer

wnd_dup_suc :: Int -> Env -> Stack -> Name -> Lab -> Term -> IO Term
wnd_dup_suc d e s k l p = do
  when debug $ putStrLn $ "## wnd_dup_suc          : " ++ show (Dup k l (Suc p) (dp d k))
  inc_inters e
  (n0,n1) <- clone e l p
  let val0 = Suc n0
  let val1 = Suc n1
  if d == 0 then do
    subst e k val1
    wnf e s val0
  else do
    subst e k val0
    wnf e s val1

wnd_dup_nam :: Int -> Env -> Stack -> Name -> Lab -> String -> IO Term
wnd_dup_nam d e s k _ n = do
  when debug $ putStrLn $ "## wnd_dup_nam          : " ++ show (Dup k (name_to_int "_") (Nam n) (dp d k))
  inc_inters e
  subst e k (Nam n)
  wnf e s (Nam n)

wnd_dup_dry :: Int -> Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnd_dup_dry d e s k l vf vx = do
  when debug $ putStrLn $ "## wnd_dup_dry          : " ++ show (Dup k l (Dry vf vx) (dp d k))
  inc_inters e
  (f0,f1) <- clone e l vf
  (x0,x1) <- clone e l vx
  let val0 = Dry f0 x0
  let val1 = Dry f1 x1
  if d == 0 then do
    subst e k val1
    wnf e s val0
  else do
    subst e k val0
    wnf e s val1

-- WNF: Ref
-- --------

wnf_ref_app :: Env -> Semi -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_app e sp func s m p = do
  when debug $ putStrLn $ "## wnf_ref_app        : " ++ show (semi_term sp) ++ " " ++ show func
  case s of
    FDp0 k l : s' -> wnf_ref_app_dp0 e sp func s' m p k l
    FDp1 k l : s' -> wnf_ref_app_dp1 e sp func s' m p k l
    _ -> case func of
      Lam k g   -> wnf_ref_app_lam e sp k g s m p
      Swi z sc  -> wnf_ref_app_swi e sp z sc s m p
      Sup k a b -> wnf_ref_app_sup e sp k a b s m p
      Era       -> wnf_ref_app_del e sp s m p
      _         -> wnf_ref_app_ret e sp func s m p

wnf_ref_app_dp0 :: Env -> Semi -> Term -> Stack -> Subs -> Path -> Name -> Lab -> IO Term
wnf_ref_app_dp0 e sp func s m p _k l = wnf_ref_app e sp func s m (p ++ [(l, 0)])

wnf_ref_app_dp1 :: Env -> Semi -> Term -> Stack -> Subs -> Path -> Name -> Lab -> IO Term
wnf_ref_app_dp1 e sp func s m p _k l = wnf_ref_app e sp func s m (p ++ [(l, 1)])

wnf_ref_app_lam :: Env -> Semi -> Name -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_lam e sp k g s m p =
  case s of
    FApp a : s' -> do
      inc_inters e
      let a' = wnf_ref_bind a p
      let m' = IM.insert k a' m
      let sp' = semi_app sp (Var k)
      wnf_ref_app e sp' g s' m' p
    _ -> wnf_ref_app_ret e sp (Lam k g) s m p

wnf_ref_app_swi :: Env -> Semi -> Term -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_swi e sp z sc s m p =
  case s of
    FApp t : s' -> do
      t_val <- wnf e [] t
      case t_val of
        Zer -> do
          inc_inters e
          let sp' = semi_app sp Zer
          wnf_ref_app e sp' z s' m p
        Suc a -> do
          inc_inters e
          let sp' = semi_ctr sp
          wnf_ref_app e sp' sc (FApp a : s') m p
        Sup l a b -> do
          inc_inters e
          (s0, s1) <- clone_ref_stack e l s'
          (m0, m1) <- clone_ref_subst e l m
          r0       <- wnf_ref_app e sp (Swi z sc) (FApp a : s0) m0 (p ++ [(l, 0)])
          r1       <- wnf_ref_app e sp (Swi z sc) (FApp b : s1) m1 (p ++ [(l, 1)])
          return (Sup l r0 r1)
        Era -> do
          return Era
        _ -> do
          wnf_ref_app_stuck e sp (FApp t_val : s') m p
    _ -> wnf_ref_app_ret e sp (Swi z sc) s m p

wnf_ref_app_sup :: Env -> Semi -> Lab -> Term -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_sup e sp k a b s m p =
  case lookup_path k p of
    Just 0 -> do
      let p' = remove_path k p
      wnf_ref_app e sp a s m p'
    Just 1 -> do
      let p' = remove_path k p
      wnf_ref_app e sp b s m p'
    Nothing -> do
      (s0, s1) <- clone_ref_stack e k s
      (m0, m1) <- clone_ref_subst e k m
      r0 <- wnf_ref_app e sp a s0 m0 p
      r1 <- wnf_ref_app e sp b s1 m1 p
      return (Sup k r0 r1)

wnf_ref_app_del :: Env -> Semi -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_del _e _sp _s _m _p = return Era

wnf_ref_app_ret :: Env -> Semi -> Term -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_ret e _sp t s m p = do
  t <- alloc e m t
  t <- wnf_ref_wrap e t p
  wnf e s t

lookup_path :: Lab -> Path -> Maybe Int
lookup_path k = go Nothing where
  go acc [] = acc
  go acc ((l,d):ps)
    | k == l    = go (Just d) ps
    | otherwise = go acc ps

remove_path :: Lab -> Path -> Path
remove_path k p =
  case break ((== k) . fst) (reverse p) of
    (_, [])    -> p
    (xs, _:ys) -> reverse (xs ++ ys)

wnf_ref_app_stuck :: Env -> Semi -> Stack -> Subs -> Path -> IO Term
wnf_ref_app_stuck e sp s m p = do
  t <- alloc e m (semi_term sp)
  t <- wnf_unwind e s t
  wnf_ref_wrap e t p

wnf_ref_bind :: Term -> Path -> Term
wnf_ref_bind x []        = x
wnf_ref_bind x ((l,0):p) = Sup l (wnf_ref_bind x p) Era
wnf_ref_bind x ((l,1):p) = Sup l Era (wnf_ref_bind x p)

wnf_ref_wrap e t []        = return t
wnf_ref_wrap e t ((l,d):p) = do
  k <- fresh e
  f <- return $ case d of { 0 -> Dp0 ; 1 -> Dp1 }
  t <- return $ Dup k l t (f k)
  wnf_ref_wrap e t p

-- Allocation
-- ==========

type Holders = IORef (IM.IntMap Name)

alloc :: Env -> Subs -> Term -> IO Term
alloc e subs term = do
  holders <- newIORef IM.empty
  alloc_term e holders subs term

alloc_term :: Env -> Holders -> Subs -> Term -> IO Term
alloc_term e holders subs term = case term of

  Var k -> do
    case IM.lookup k subs of
      Nothing -> error $ "unbound variable: " ++ int_to_name k
      Just v  -> alloc_var e holders k 0 v

  Dp0 k -> do
    case IM.lookup k subs of
      Just (Var k) -> alloc_var e holders k 1 (Dp0 k)
      _            -> error $ "unbound variable: " ++ int_to_name k ++ "₀"

  Dp1 k -> do
    case IM.lookup k subs of
      Just (Var k) -> alloc_var e holders k 2 (Dp1 k)
      _            -> error $ "unbound variable: " ++ int_to_name k ++ "₁"

  Era -> do
    return Era

  Sup l a b -> do
    a' <- alloc_term e holders subs a
    b' <- alloc_term e holders subs b
    return (Sup l a' b')

  Dup k l v t -> do
    k' <- fresh e
    v' <- alloc_term e holders subs v
    t' <- alloc_term e holders (IM.insert k (Var k') subs) t
    return (Dup k' l v' t')

  Set -> do
    return Set

  All a b -> do
    a' <- alloc_term e holders subs a
    b' <- alloc_term e holders subs b
    return (All a' b')

  Lam k f -> do
    k' <- fresh e
    f' <- alloc_term e holders (IM.insert k (Var k') subs) f
    return (Lam k' f')

  App f x -> do
    f' <- alloc_term e holders subs f
    x' <- alloc_term e holders subs x
    return (App f' x')

  Nat -> do
    return Nat

  Zer -> do
    return Zer

  Suc n -> do
    n' <- alloc_term e holders subs n
    return (Suc n')

  Ref k -> do
    return (Ref k)

  Nam x -> do
    return (Nam x)

  Dry f x -> do
    f' <- alloc_term e holders subs f
    x' <- alloc_term e holders subs x
    return (Dry f' x')

  Swi z s -> do
    z' <- alloc_term e holders subs z
    s' <- alloc_term e holders subs s
    return (Swi z' s')

alloc_var :: Env -> Holders -> Name -> Int -> Term -> IO Term
alloc_var e holders k tag v = do
  hs <- readIORef holders
  let key = (k `shiftL` 2) + tag
  case IM.lookup key hs of
    Nothing -> do
      h <- fresh e
      subst e h v
      writeIORef holders (IM.insert key h hs)
      return (Var h)
    Just old_h -> do
      m_prev <- take_sub e old_h
      case m_prev of
        Nothing -> do
          error "unreachable"
        Just v_prev -> do
          (d0, d1) <- clone e 0 v_prev
          subst e old_h d0
          new_h <- fresh e
          subst e new_h d1
          writeIORef holders (IM.insert key new_h hs)
          return (Var new_h)

-- Normalization
-- =============

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x <- wnf e [] x
  case x of
    Var k -> do
      return (Var k)
    Dp0 k -> do
      return (Dp0 k)
    Dp1 k -> do
      return (Dp1 k)
    Era -> do
      return Era
    Sup l a b -> do
      a <- snf e d a
      b <- snf e d b
      return (Sup l a b)
    Dup k l v t -> do
      make_dup e k l (Sup l (Nam (int_to_name d ++ "₀")) (Nam (int_to_name d ++ "₁")))
      v <- snf e d v
      t <- snf e d t
      return (Dup d l v t)
    Set -> do
      return Set
    All a b -> do
      a <- snf e d a
      b <- snf e d b
      return (All a b)
    Lam k f -> do
      subst e k (Nam (int_to_name d))
      f <- snf e (d + 1) f
      return (Lam d f)
    App f x -> do
      f <- snf e d f
      x <- snf e d x
      return (App f x)
    Nat -> do
      return Nat
    Zer -> do
      return Zer
    Suc p -> do
      p <- snf e d p
      return (Suc p)
    Swi z s -> do
      z <- snf e d z
      s <- snf e d s
      return (Swi z s)
    Ref k -> do
      return (Ref k)
    Nam k -> do
      return (Nam k)
    Dry f x -> do
      f <- snf e d f
      x <- snf e d x
      return (Dry f x)

-- Collapsing
-- ==========

collapse :: Env -> Term -> IO Term
collapse e x = do
  !x' <- wnf e [] x
  case x' of
    Era -> return Era
    Sup l a b -> do
      a' <- collapse e a
      b' <- collapse e b
      return $ Sup l a' b'
    Set -> return Set
    All a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      collapse_inject e (Lam aV (Lam bV (All (Var aV) (Var bV)))) [a',b']
    Lam k f -> do
      fV <- fresh e
      f' <- collapse e f
      collapse_inject e (Lam fV (Lam k (Var fV))) [f']
    App f x1 -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x1
      collapse_inject e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Nat -> return Nat
    Zer -> return Zer
    Suc p -> do
      pV <- fresh e
      p' <- collapse e p
      collapse_inject e (Lam pV (Suc (Var pV))) [p']
    Swi z s -> do
      z' <- collapse e z
      s' <- collapse e s
      return (Swi z' s')
    Nam n -> return $ Nam n
    Dry f x1 -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x1
      collapse_inject e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    x'' -> return x''

collapse_inject :: Env -> Term -> [Term] -> IO Term
collapse_inject e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    Sup l a b -> do
      (f0  , f1 ) <- clone  e l f
      (xs0 , xs1) <- clones e l xs
      a' <- collapse_inject e f0 (a : xs0)
      b' <- collapse_inject e f1 (b : xs1)
      return $ Sup l a' b'
    x'' -> collapse_inject e (App f x'') xs
collapse_inject _ f [] = return f

-- Equality
-- ========

equal :: Env -> Int -> Term -> Term -> IO Bool
equal e d a b = do
  !a <- wnf e [] a
  !b <- wnf e [] b
  case (a, b) of
    (Sup l a1 a2, _) -> do
      (b1, b2) <- clone e l b
      e1 <- equal e d a1 b1
      e2 <- equal e d a2 b2
      return (e1 && e2)
    (_, Sup l b1 b2) -> do
      (a1, a2) <- clone e l a
      e1 <- equal e d a1 b1
      e2 <- equal e d a2 b2
      return (e1 && e2)
    (Era, Era) -> do
      return True
    (Set, Set) -> do
      return True
    (All a1 a2, All b1 b2) -> do
      e1 <- equal e d a1 b1
      e2 <- equal e d a2 b2
      return (e1 && e2)
    (Lam k1 f1, Lam k2 f2) -> do
      let nam = Nam (int_to_name d)
      subst e k1 nam
      subst e k2 nam
      equal e (d + 1) f1 f2
    (App f1 x1, App f2 x2) -> do
      ef <- equal e d f1 f2
      ex <- equal e d x1 x2
      return (ef && ex)
    (Nat, Nat) -> do
      return True
    (Zer, Zer) -> do
      return True
    (Suc a1, Suc b1) -> do
      equal e d a1 b1
    (Swi z1 s1, Swi z2 s2) -> do
      ez <- equal e d z1 z2
      es <- equal e d s1 s2
      return (ez && es)
    (Ref k1, Ref k2) -> do
      return (k1 == k2)
    (Nam n1, Nam n2) -> do
      return (n1 == n2)
    (Dry f1 x1, Dry f2 x2) -> do
      ef <- equal e d f1 f2
      ex <- equal e d x1 x2
      return (ef && ex)
    (Var _, _) -> error "equal: unexpected Var"
    (_, Var _) -> error "equal: unexpected Var"
    (Dp0 _, _) -> error "equal: unexpected Dp0"
    (_, Dp0 _) -> error "equal: unexpected Dp0"
    (Dp1 _, _) -> error "equal: unexpected Dp1"
    (_, Dp1 _) -> error "equal: unexpected Dp1"
    _ -> do return False

-- SupGen
-- ======

max_elim :: Int
max_elim = 2

max_intr :: Int
max_intr = 2

rec_intr :: Int
rec_intr = 1

-- e: Env    = environment
-- l: Int    = label (for forking the search space)
-- d: Int    = depth (lam binders, used for internal variable names)
-- k: Int    = budget (max_elim/intr)
-- t: Term   = goal type
-- s: Semi   = spine/lhs (represented as application chain)
-- f: [Term] = folds (list of spines eligible for recursion)
-- r: Ann    = recursion (the function itself)
-- b: [Ann]  = library (external fns)
-- c: [Ann]  = context (internal vars)

type Ann   = (Term,Term)
type Gen a = Env -> Int -> Int -> Int -> Term -> Semi -> [Term] -> Ann -> [Ann] -> [Ann] -> IO a

-- Utils for SupGen
-- ----------------

sp0 :: Int -> Int
sp0 x = (x * 16293 + 1) `mod` 65536

sp1 :: Int -> Int
sp1 x = (x * 32677 + 3) `mod` 65536

-- Helper function to extract arguments from a spine Term (application chain).
-- Corresponds to Term/LHS/to_list in Bend.
lhs_to_list :: Term -> [Term]
lhs_to_list tm = reverse (go tm [])
  where go (App f x) acc = go f (x:acc)
        go _ acc = acc

-- Folding
-- -------

-- def Term/gen/Fol/arg(...) -> Term/gen/Fol:
-- Applies arg to each spine in fol.
gen_fol_arg :: Env -> [Term] -> Term -> IO [Term]
gen_fol_arg e f arg = do -- FIXME: this is using arg non linearly
  return $ map (\rxs -> App rxs arg) f

-- Pattern-Matcher (LHS)
-- ---------------------

-- def Term/gen/lam(...) -> Term:
gen_lam :: Gen Term
gen_lam e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_lam :: " ++ show t
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (t0, t1) <- clone   e tl t
      -- (f0, f1) <- clones  e tl f
      -- (r0, r1) <- clone2  e tl r
      -- (b0, b1) <- clone2s e tl b
      -- (c0, c1) <- clone2s e tl c
      -- fork0    <- gen_lam e l d k t0 s f0 r0 b0 c0
      -- fork1    <- gen_lam e l d k t1 s f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      gen_lam_all e l d k t_wnf s f r b c
    t' -> do
      gen_body e l d k t' s f r b c

-- def Term/gen/lam/all(...) -> Term:
gen_lam_all :: Gen Term
gen_lam_all e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_lam_all :: " ++ show t
  -- In Bend, this function checks if A is frozen. We skip that distinction here.
  gen_lam_all_try e l d k t s f r b c

-- def Term/gen/lam/all/try(...) -> Term:
gen_lam_all_try :: Gen Term
gen_lam_all_try e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_lam_all_try (K=" ++ show k ++ ")"
  if k == 0 then do
    gen_lam_var e l d 0 t s f r b c
  else do
    (t0, t1) <- clone   e l t
    (f0, f1) <- clones  e l f
    (r0, r1) <- clone2  e l r
    (b0, b1) <- clone2s e l b
    (c0, c1) <- clone2s e l c
    fork0    <- gen_lam_var e (sp0 l) d k     t0 s f0 r0 b0 c0
    fork1    <- gen_lam_mat e (sp1 l) d (k-1) t1 s f1 r1 b1 c1
    return $ Sup l fork0 fork1

-- def Term/gen/lam/var(...) -> Term:
gen_lam_var :: Gen Term
gen_lam_var e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_lam_var"
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (f0, f1) <- clones  e tl f
      -- (r0, r1) <- clone2  e tl r
      -- (b0, b1) <- clone2s e tl b
      -- (c0, c1) <- clone2s e tl c
      -- fork0    <- gen_lam_var e l d k t0 s f0 r0 b0 c0
      -- fork1    <- gen_lam_var e l d k t1 s f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    (All ta tb) -> do
      x  <- fresh e
      xv <- return $ Nam (int_to_name d)
      s' <- return $ semi_app s xv
      f' <- gen_fol_arg e f xv
      c' <- return $ c ++ [(xv, ta)]
      t' <- return $ App tb xv
      fn <- gen_lam e l (d + 1) k t' s' f' r b c'
      return $ Lam x fn
    _ -> do
      return Era -- Cannot introduce lambda if type is not All.

gen_lam_mat :: Gen Term
gen_lam_mat e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_lam_mat"
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (f0, f1) <- clones  e tl f
      -- (r0, r1) <- clone2  e tl r
      -- (b0, b1) <- clone2s e tl b
      -- (c0, c1) <- clone2s e tl c
      -- fork0    <- gen_lam_mat e l d k t0 s f0 r0 b0 c0
      -- fork1    <- gen_lam_mat e l d k t1 s f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      !a_wnf <- wnf e [] ta
      case a_wnf of
        Era -> do
          return Era
        Sup tl a0 a1 -> do
          error "TODO"
          -- (f0, f1)   <- clones  e tl f
          -- (r0, r1)   <- clone2  e tl r
          -- (b0, b1)   <- clone2s e tl b
          -- (c0, c1)   <- clone2s e tl c
          -- (tb0, tb1) <- clone   e tl tb
          -- fork0      <- gen_lam_mat e l d k (All a0 tb0) s f0 r0 b0 c0
          -- fork1      <- gen_lam_mat e l d k (All a1 tb1) s f1 r1 b1 c1
          -- return $ Sup tl fork0 fork1
        Nat -> do
          -- Clones due to truly duplicated usage (not a fork)
          (tb0, tb1) <- clone   e 0 tb
          (f0, f1)   <- clones  e 0 f
          (r0, r1)   <- clone2  e 0 r
          (b0, b1)   <- clone2s e 0 b
          (c0, c1)   <- clone2s e 0 c
          n          <- fresh e
          m          <- fresh e
          p          <- fresh e
          z_t        <- return $ App tb0 Zer
          z_s        <- return $ semi_app s Zer
          z_f        <- gen_fol_arg e f0 Zer
          z_x        <- gen_lam e (sp0 l) d k z_t z_s z_f r0 b0 c0
          s_t        <- return $ All Nat (Lam n (App tb1 (Suc (Var n))))
          s_s        <- return $ semi_ctr s
          s_f        <- return $ App (semi_term s) (Lam p (Var p)) : f1
          s_x        <- gen_lam e (sp1 l) d k s_t s_s s_f r1 b1 c1
          return $ Swi z_x s_x
        _ -> do -- Cannot match on this argument type.
          return Era
    _ -> do -- Cannot match if type is not All.
      return Era

-- def Term/gen/body(...) -> Term:
gen_body :: Gen Term
gen_body e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_body :: " ++ show t
  gen_expr e l d max_intr t s f r b c

-- Enumerator (RHS)
-- ----------------

-- def Term/gen/expr(...) -> Term:
gen_expr :: Gen Term
gen_expr e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_expr (K=" ++ show k ++ ") :: " ++ show t
  if k == 0 then do
    return Zer
    -- gen_pick e l d 0 t s f r b c
  else do
    (t0, t1) <- clone   e l t
    (f0, f1) <- clones  e l f
    (r0, r1) <- clone2  e l r
    (b0, b1) <- clone2s e l b
    (c0, c1) <- clone2s e l c
    fork0    <- gen_intr e (sp0 l) d (k-1) t0 s f0 r0 b0 c0
    -- fork0    <- return $ Zer
    fork1    <- gen_pick e (sp1 l) d k t1 s f1 r1 b1 c1
    -- fork1    <- return $ Zer
    return $ Sup l fork0 fork1

-- Introduce Constructor
-- ---------------------

-- def Term/gen/intr(...) -> Term:
gen_intr :: Gen Term
gen_intr e l d k t s f r b c = do
  when debug $ putStrLn $ "gen_intr (K=" ++ show k ++ ") :: " ++ show t
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (f0, f1) <- clones  e tl f
      -- (r0, r1) <- clone2  e tl r
      -- (b0, b1) <- clone2s e tl b
      -- (c0, c1) <- clone2s e tl c
      -- fork0    <- gen_intr e l d k t0 s f0 r0 b0 c0
      -- fork1    <- gen_intr e l d k t1 s f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    Nat -> do
      (f0, f1) <- clones  e l f
      (r0, r1) <- clone2  e l r
      (b0, b1) <- clone2s e l b
      (c0, c1) <- clone2s e l c
      fork0    <- return $ Zer
      pred     <- gen_expr e (sp1 l) d k Nat s f1 r1 b1 c1
      fork1    <- return $ Suc pred
      return $ Sup l fork0 fork1
    All ta tb -> do
      error "TODO"
    _ -> do
      return Era -- Cannot introduce constructor for this type.

-- Pick (Elimination/Application)
-- ------------------------------

gen_pick :: Gen Term
gen_pick e l d k t s f r b c = do
  gen_pick_lib e l d k t s f r b c

gen_pick_lib :: Gen Term
gen_pick_lib e l d k t s f r b c = do
  case b of
    [] -> do
      gen_pick_fol e l d k t s f r [] c
    ((tm, ty) : bs) -> do
      (t0, t1)   <- clone   e l t
      (f0, f1)   <- clones  e l f
      (r0, r1)   <- clone2  e l r
      (c0, c1)   <- clone2s e l c
      (bs0, bs1) <- clone2s e l bs
      fork0      <- gen_call e (sp0 l) d k t0 s f0 r0 bs0 c0 tm ty
      fork1      <- gen_pick_lib e (sp1 l) d k t1 s f1 r1 bs1 c1
      return $ Sup l fork0 fork1

gen_pick_fol :: Gen Term
gen_pick_fol e l d k t s f r b c = do
  case f of
    [] -> do
      gen_pick_ctx e l d k t s [] r b c
    (rxs : fs) -> do
      (t0, t1)     <- clone   e l t
      (b0, b1)     <- clone2s e l b
      (c0, c1)     <- clone2s e l c
      (r0, r1)     <- clone2  e l r
      (fs0, fs1)   <- clones  e l fs
      (tm0, ty0)   <- return $ r0
      (tm0A, tm0B) <- clone e l tm0
      (ty0A, ty0B) <- clone e l ty0
      fork0        <- gen_fold e (sp0 l) d k t0 s [] (tm0A,ty0A) b0 c0 (lhs_to_list rxs) tm0B ty0B
      fork1        <- gen_pick_fol e (sp1 l) d k t1 s fs1 r1 b1 c1
      return $ Sup l fork0 fork1

gen_pick_ctx :: Gen Term
gen_pick_ctx e l d k t s f r b c = do
  case c of
    [] -> do
      return Era
    [(tm, ty)] -> do
      gen_call e l d k t s f r b [] tm ty
    ((tm, ty) : cs) -> do
      (t0, t1)   <- clone   e l t
      (f0, f1)   <- clones  e l f
      (r0, r1)   <- clone2  e l r
      (b0, b1)   <- clone2s e l b
      (cs0, cs1) <- clone2s e l cs
      fork0      <- gen_call e (sp0 l) d k t0 s f0 r0 b0 cs0 tm ty
      fork1      <- gen_pick_ctx e (sp1 l) d k t1 s f1 r1 b1 cs1
      return $ Sup l fork0 fork1

-- Callers
-- -------

-- def Term/gen/fold(...) -> Term:
gen_fold :: Env -> Int -> Int -> Int -> Term -> Semi -> [Term] -> Ann -> [Ann] -> [Ann] -> [Term] -> Term -> Term -> IO Term
gen_fold e l d k t s f r b c args tm ty = do
  case args of
    [] -> do
      gen_call e l d rec_intr t s f r b c tm ty
    (arg : args_rest) -> do
      !ty_wnf <- wnf e [] ty
      case ty_wnf of
        Era -> do
          return Era
        Sup tl t0 t1 -> do
          error "TODO"
        All ta tb -> do
          let tm' = App tm arg
          let ty' = App tb arg
          gen_fold e l d k t s f r b c args_rest tm' ty'
        _ -> do
          return Era -- Type mismatch: expected All type.

gen_call :: Env -> Int -> Int -> Int -> Term -> Semi -> [Term] -> Ann -> [Ann] -> [Ann] -> Term -> Term -> IO Term
gen_call e l d k t s f r b c tm ty = do
  when debug $ putStrLn $ "gen_call (K=" ++ show k ++ ") :: " ++ show tm ++ " : " ++ show ty ++ " |- " ++ show t
  !ty_wnf <- wnf e [] ty
  case ty_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (t0, t1)   <- clone   e tl t
      -- (f0, f1)   <- clones  e tl f
      -- (r0, r1)   <- clone2  e tl r
      -- (b0, b1)   <- clone2s e tl b
      -- (c0, c1)   <- clone2s e tl c
      -- (tm0, tm1) <- clone   e tl tm
      -- fork0      <- gen_call e l d k t0 s f0 r0 b0 c0 tm0 ty0
      -- fork1      <- gen_call e l d k t1 s f1 r1 b1 c1 tm1 ty1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      (f0, f1) <- clones  e l f
      (r0, r1) <- clone2  e l r
      (b0, b1) <- clone2s e l b
      (c0, c1) <- clone2s e l c
      arg      <- gen_expr e (sp0 l) d k ta s f0 r0 b0 c0
      let tm'  = App tm arg
      let ty'  = App tb arg
      fun <- gen_call e (sp1 l) d k t s f1 r1 b1 c1 tm' ty'
      return fun
    ty -> do
      eq <- equal e d ty t
      if eq then do
        return tm
      else do
        return Era

-- Main
-- ====

flatten :: Term -> [Term]
flatten term = bfs [term] [] where
  bfs []     acc = reverse acc
  bfs (t:ts) acc = case t of
    Sup _ a b -> bfs (ts ++ [a, b]) acc
    _         -> bfs ts (t : acc)

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
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(@and 0 a)")
  , ("λx.(@and x 0)", "λa.(@and a 0)")
  , ("(@dup 3)", "λa.(a 3 3)")
  , ("λk.(@dup k)", "λa.λb.(b a a)")
  , ("(@sum 1+1+1+0)", "6")
  , ("λx.(@sum 1+1+1+x)", "λa.3+(@add a 2+(@add a 1+(@add a (@sum a))))")
  , ("(@foo 0)", "&L{0,0}")
  , ("(@foo 3)", "&L{3,2}")
  , ("(@dbl 3)", "6")
  , ("λx.(@dbl 2+x)", "λa.4+(@dbl a)")
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
  , "@id  = λa.a"
  , "@dup = λx. λt. (t x x)"
  , "@not = λ{0:1+0;1+:λp.0}"
  , "@dbl = λ{0:0;1+:λp.2+(@dbl p)}"
  , "@and = λ{0:λ{0:0;1+:λp.0};1+:λp.λ{0:0;1+:λp.1+0}}"
  , "@add = λ{0:λb.b;1+:λa.λb.1+(@add a b)}"
  , "@sum = λ{0:0;1+:λp.1+(@add p (@sum p))}"
  , "@foo = &L{λx.x,λ{0:0;1+:λp.p}}"
  -- , "@gen = !F&A=@gen &A{λx.!X&B=x;&B{X₀,1+X₁},λ{0:&C{0,1};1+:λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  ]

run :: String -> String -> IO ()
run book_src term_src = do
  !env <- new_env $ read_book book_src
  !ini <- getCPUTime
  !val <- alloc env IM.empty (read_term term_src)
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

test :: IO ()
test = forM_ tests $ \ (src, expd) -> do
  env <- new_env $ read_book book
  det <- collapse env $ read_term src
  det <- show <$> snf env 1 det
  if det == expd then do
    putStrLn $ "[PASS] " ++ src ++ " -> " ++ det
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ expd
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = test
-- main = do
  -- !env <- new_env $ read_book book
  -- !typ <- return $ All Nat (Lam 0 Nat)
  -- !val <- gen_lam env 1 0 2 typ (semi_new 0) [] (Nam "F", typ) [] []
  -- print $ val
  -- !val <- return $ flatten val
  -- forM_ val $ \ x -> do
    -- print $ x
