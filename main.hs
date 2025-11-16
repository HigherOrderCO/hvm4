-- Calculus of Interactions
-- ========================
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
-- | Ref ::= "@" Name
-- | Cal ::= Term "~>" Term
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
-- ! X &L = Λ{0:z;1+:s}
-- -------------------- dup-swi
-- ! Z &L = z
-- ! S &L = s
-- X₀ ← Λ{0:Z₀;1+:S₀}
-- X₁ ← Λ{0:Z₁;1+:S₁}
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
-- ! X &L = f ~> g
-- --------------- dup-cal
-- ! F &L = f
-- ! G &L = g
-- X₀ ← F₀ ~> G₀
-- X₁ ← F₁ ~> G₁
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
-- ((f ~> &{}) a)
-- -------------- app-cal-era
-- &{}
--
-- ((f ~> &L{x,y}) a)
-- ------------------ app-cal-sup
-- ! F &L = f
-- ! A &L = a
-- &L{((F₀ ~> x) A₀)
--   ,((F₁ ~> y) A₁)}
--
-- ((f ~> λx.g) a)
-- --------------- app-cal-lam
-- x ← a
-- (f x) ~> g
--
-- ((f ~> Λ{0:z;1+:s}) &{})
-- ------------------------ app-cal-swi-era
-- &{}
--
-- ((f ~> Λ{0:z;1+:s}) &L{a,b})
-- ---------------------------- app-cal-swi-sup
-- ! F &L = f
-- ! Z &L = z
-- ! S &L = s
-- &L{((F₀ ~> Λ{0:Z₀;1+:S₀}) a)
--   ,((F₁ ~> Λ{0:Z₁;1+:S₁}) b)}
--
-- ((f ~> Λ{0:z;1+:s}) 1+n)
-- ------------------------ app-cal-swi-suc
-- ((λp.(f 1+p) ~> s) n)
--
-- ((f ~> Λ{0:z;1+:s}) 0)
-- ---------------------- app-cal-swi-zer
-- (f 0) ~> z
--
-- @foo
-- ------------------ ref
-- foo ~> Book["foo"]

{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

import Control.Monad (forM_)
import Data.Bits (shiftL)
import Data.Char (isDigit)
import Data.IORef
import Data.List (foldl', elemIndex)
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

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
  | Swi !Term !Term
  | Ref !Name
  | Nam !String
  | Dry !Term !Term
  | Cal !Term !Term
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
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show Set           = "*"
  show (All a b)     = "∀" ++ show a ++ "." ++ show b                                 --
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f [x]
  show Nat           = "ℕ"
  show Zer           = "0"
  show (Suc p)       = show_add 1 p
  show (Swi z s)     = "λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = k
  show (Dry f x)     = show_app f [x]
  show (Cal f g)     = show f ++ "~>" ++ show g

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

show_dup_map :: IM.IntMap (Lab, Term) -> String
show_dup_map m = unlines [ "! " ++ int_to_name k ++ " &" ++ int_to_name l ++ " = " ++ show v | (k, (l, v)) <- IM.toList m ]

show_sub_map :: IM.IntMap Term -> String
show_sub_map m = unlines [ int_to_name (k `div` 4) ++ suffix (k `mod` 4) ++ " ← " ++ show v | (k, v) <- IM.toList m ]
  where suffix x = case x of { 0 -> "" ; 1 -> "₀" ; 2 -> "₁" ; _ -> "?" }

-- Name Encoding/Decoding
-- ======================

-- Base-64 encoding (for parsing user names/labels and printing)
-- Alphabet: _ (0), a-z (1-26), A-Z (27-52), 0-9 (53-62), $ (63).
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
  [ parse_lam_or_swi
  , parse_dup
  , parse_app
  , parse_sup
  , parse_era
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

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  lexeme (choice [char 'λ', char '\\'])
  parse_swi_body <++ parse_lam_body

parse_lam_body :: ReadP Term
parse_lam_body = do
  k <- parse_nam
  lexeme (char '.')
  body <- parse_term
  return (Lam (name_to_int k) body)

parse_swi_body :: ReadP Term
parse_swi_body = do
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

parse_func :: ReadP (Name, Term)
parse_func = do
  lexeme (char '@')
  k <- parse_nam
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

subst :: Kind -> Env -> Name -> Term -> IO ()
subst s e k v = modifyIORef' (env_sub_map e) (IM.insert (k `shiftL` 2 + fromEnum s) v)

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

clone_pair :: Env -> Lab -> (Term,Term) -> IO ((Term,Term),(Term,Term))
clone_pair e l (x,y) = do
  (x0,x1) <- clone e l x
  (y0,y1) <- clone e l y
  return ((x0,y0),(x1,y1))

clone_pair_list :: Env -> Lab -> [(Term,Term)] -> IO ([(Term,Term)],[(Term,Term)])
clone_pair_list e l []         = return $ ([],[])
clone_pair_list e l (xy : xys) = do
  (xy0  , xy1 ) <- clone_pair e l xy
  (xys0 , xys1) <- clone_pair_list e l xys
  return $ (xy0 : xys0, xy1 : xys1)

-- WNF: Weak Normal Form
-- =====================

data Frame
  = FApp Term
  | FDp0 Name Lab
  | FDp1 Name Lab

type Stack = [Frame]

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

-- WNF: Enter
-- ----------

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
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- alloc e f
      wnf_enter e s (Cal (Nam ("@" ++ int_to_name k)) g)
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

wnf_enter e s (Cal f g) = do
  wnf_unwind e s (Cal f g)

wnf_enter e s f = do
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []      v = return v
wnf_unwind e (x : s) v = do
  case x of
    FApp a   -> wnf_app e s v a
    FDp0 k l -> wnf_dup e s v k l (Dp0 k)
    FDp1 k l -> wnf_dup e s v k l (Dp1 k)

wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s f a = case f of
  Era       -> wnf_app_era e s f a
  Sup {}    -> wnf_app_sup e s f a
  Lam {}    -> wnf_app_lam e s f a
  Swi {}    -> error "TODO"
  Nam {}    -> wnf_app_nam e s f a
  Dry {}    -> wnf_app_dry e s f a
  Cal {}    -> wnf_app_cal e s f a
  Set       -> error "wnf_app_set"
  All {}    -> error "wnf_app_all"
  Nat       -> error "wnf_app_nat"
  Zer       -> error "wnf_app_zer"
  Suc {}    -> error "wnf_app_suc"
  _         -> wnf_unwind e s (App f a)

wnf_dup :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup e s v k l t = case v of
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
  Cal {} -> wnf_dup_cal e s v k l t
  _      -> wnf_unwind e s (Dup k l v t)

-- WNF: Sub Interaction
-- --------------------

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s $ case ki of
      VAR -> Var k
      DP0 -> Dp0 k
      DP1 -> Dp1 k

-- WNF: App Interactions
-- ---------------------

type WnfApp = Env -> Stack -> Term -> Term -> IO Term

wnf_app_era :: WnfApp
wnf_app_era e s Era v = do
  inc_inters e
  wnf e s Era

wnf_app_nam :: WnfApp
wnf_app_nam e s (Nam fk) v = wnf e s (Dry (Nam fk) v)

wnf_app_dry :: WnfApp
wnf_app_dry e s (Dry ff fx) v = wnf e s (Dry (Dry ff fx) v)

wnf_app_lam :: WnfApp
wnf_app_lam e s (Lam fx ff) v = do
  inc_inters e
  subst VAR e fx v
  wnf e s ff

wnf_app_sup :: WnfApp
wnf_app_sup e s (Sup fL fa fb) v = do
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

-- WNF: Dup Interactions
-- ---------------------

type WnfDup = Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term

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

-- WNF: Deref Interactions
-- -----------------------

wnf_app_cal :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_cal e s (Cal f g) a = do
  !g_wnf <- wnf e [] g
  case g_wnf of
    Era    -> wnf_app_cal_era e s f g_wnf a
    Sup {} -> wnf_app_cal_sup e s f g_wnf a
    Lam {} -> wnf_app_cal_lam e s f g_wnf a
    Swi {} -> wnf_app_cal_swi e s f g_wnf a
    Set    -> error "wnf_app_cal_set"
    All {} -> error "wnf_app_cal_all"
    Nat    -> error "wnf_app_cal_nat"
    Zer    -> error "wnf_app_cal_zer"
    Suc {} -> error "wnf_app_cal_suc"
    Nam {} -> error "wnf_app_cal_nam"
    Dry {} -> error "wnf_app_cal_dry"
    Cal {} -> error "wnf_app_cal_cal"
    _      -> wnf_unwind e s (App (Cal f g_wnf) a)

wnf_app_cal_era :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_era e s f Era a = do
  inc_inters e
  wnf e s Era

wnf_app_cal_sup :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_sup e s f (Sup l x y) a = do
  inc_inters e
  (f0,f1) <- clone e l f
  (a0,a1) <- clone e l a
  let app0 = (App (Cal f0 x) a0)
  let app1 = (App (Cal f1 y) a1)
  wnf_enter e s (Sup l app0 app1)

wnf_app_cal_lam :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_lam e s f (Lam x g) a = do
  inc_inters e
  subst VAR e x a
  wnf_enter e s (Cal (App f (Var x)) g)

wnf_app_cal_swi :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi e s f (Swi z sc) a = do
  !a_wnf <- wnf e [] a
  case a_wnf of
    Era    -> wnf_app_cal_swi_era e s f z sc a_wnf
    Sup {} -> wnf_app_cal_swi_sup e s f z sc a_wnf
    Zer    -> wnf_app_cal_swi_zer e s f z a_wnf
    Suc {} -> wnf_app_cal_swi_suc e s f sc a_wnf
    Set    -> error "wnf_app_cal_swi_set"
    All {} -> error "wnf_app_cal_swi_all"
    Lam {} -> error "wnf_app_cal_swi_lam"
    Nat    -> error "wnf_app_cal_swi_nat"
    Swi {} -> error "wnf_app_cal_swi_swi"
    Nam {} -> error "wnf_app_cal_swi_nam"
    Dry {} -> error "wnf_app_cal_swi_dry"
    Cal {} -> error "wnf_app_cal_swi_cal"
    a      -> wnf_unwind e s (App f a)

wnf_app_cal_swi_era :: Env -> Stack -> Term -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi_era e s f z sc Era = do
  wnf_enter e s Era

wnf_app_cal_swi_sup :: Env -> Stack -> Term -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi_sup e s f z sc (Sup l a b) = do
  inc_inters e
  (f0,f1) <- clone e l f
  (z0,z1) <- clone e l z
  (s0,s1) <- clone e l sc
  let app0 = App (Cal f0 (Swi z0 s0)) a
  let app1 = App (Cal f1 (Swi z1 s1)) b
  wnf_enter e s (Sup l app0 app1)

wnf_app_cal_swi_zer :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi_zer e s f z Zer = do
  inc_inters e
  wnf_enter e s (Cal (App f Zer) z)

wnf_app_cal_swi_suc :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi_suc e s f sc (Suc n) = do
  inc_inters e
  p <- fresh e
  let fn = (Lam p (App f (Suc (Var p))))
  wnf_enter e s (App (Cal fn sc) n)

wnf_dup_cal :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup_cal e s (Cal f g) k l t = wnf_dup_2 e s k l t f g Cal

-- Allocation
-- ==========

-- Allocates a closed term, replacing all bound names with fresh ones.
alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where
  go :: IM.IntMap Name -> Term -> IO Term
  go m (Var k)       = return $ Var (IM.findWithDefault k k m)
  go m (Dp0 k)       = return $ Dp0 (IM.findWithDefault k k m)
  go m (Dp1 k)       = return $ Dp1 (IM.findWithDefault k k m)
  go _ Era           = return Era
  go m (Sup l a b)   = Sup l <$> go m a <*> go m b
  go m (Dup k l v t) = do
    k' <- fresh e
    v' <- go m v
    t' <- go (IM.insert k k' m) t
    return $ Dup k' l v' t'
  go _ Set           = return Set
  go m (All a b)     = All <$> go m a <*> go m b
  go m (Lam k f) = do
    k' <- fresh e
    f' <- go (IM.insert k k' m) f
    return $ Lam k' f'
  go m (App f x)     = App <$> go m f <*> go m x
  go _ Nat           = return Nat
  go _ Zer           = return Zer
  go m (Suc n)       = Suc <$> go m n
  go m (Swi z s)     = Swi <$> go m z <*> go m s
  go _ (Ref k)       = return $ Ref k
  go _ (Nam k)       = return $ Nam k
  go m (Dry f x)     = Dry <$> go m f <*> go m x
  go m (Cal f g)     = Cal <$> go m f <*> go m g

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
      return Era
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
      return Set
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
      return Nat
    Zer -> do
      return Zer
    Suc p -> do
      p' <- snf e d p
      return $ Suc p'
    Swi z s -> do
      z' <- snf e d z
      s' <- snf e d s
      return $ Swi z' s'
    Ref k -> do
      return $ Ref k
    Nam k -> do
      return $ Nam k
    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'
    Cal f g -> do
      g' <- snf e d g
      return g'

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
      inj e (Lam aV (Lam bV (All (Var aV) (Var bV)))) [a',b']
    (Lam k f) -> do
      fV <- fresh e
      f' <- collapse e f
      inj e (Lam fV (Lam k (Var fV))) [f']
    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inj e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Nat -> do
      return Nat
    Zer -> do
      return Zer
    (Suc p) -> do
      pV <- fresh e
      p' <- collapse e p
      inj e (Lam pV (Suc (Var pV))) [p']
    (Swi z s) -> do
      zV <- fresh e
      sV <- fresh e
      z' <- collapse e z
      s' <- collapse e s
      inj e (Lam zV (Lam sV (Swi (Var zV) (Var sV)))) [z',s']
    Nam n -> do
      return $ Nam n
    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inj e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    (Cal f g) -> do 
      collapse e g
    x -> do
      return $ x

inj :: Env -> Term -> [Term] -> IO Term
inj e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    (Sup l a b) -> do
      (f0  , f1 ) <- clone e l f
      (xs0 , xs1) <- clone_list e l xs
      a' <- inj e f0 (a : xs0)
      b' <- inj e f1 (b : xs1)
      return $ Sup l a' b'
    x' -> do
      inj e (App f x') xs
inj e f [] = do
  return $ f

-- SupGen
-- ======

max_elim :: Int
max_elim = 2

max_intr :: Int
max_intr = 2

rec_intr :: Int
rec_intr = 1

sp0 :: Int -> Int
sp0 x = (x * 16293 + 1) `mod` 65536

sp1 :: Int -> Int
sp1 x = (x * 32677 + 3) `mod` 65536

-- e: Env    = environment
-- l: Int    = label (for forking the search space)
-- d: Int    = depth (lam binders, used for internal variable names)
-- k: Int    = budget (max_elim/intr)
-- t: Term   = goal type
-- s: Term   = spine/lhs (represented as application chain)
-- f: [Term] = folds (list of spines eligible for recursion)
-- r: Ann    = recursion (the function itself)
-- b: [Ann]  = library (external fns)
-- c: [Ann]  = context (internal vars)
type Ann   = (Term,Term)
type Gen a = Env -> Int -> Int -> Int -> Term -> Term -> [Term] -> Ann -> [Ann] -> [Ann] -> IO a

-- Utils for SupGen
-- ----------------

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
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (s0, s1) <- clone   e tl s
      -- (f0, f1) <- clone_list  e tl f
      -- (r0, r1) <- clone_pair  e tl r
      -- (b0, b1) <- clone_pair_list e tl b
      -- (c0, c1) <- clone_pair_list e tl c
      -- fork0    <- gen_lam e l d k t0 s0 f0 r0 b0 c0
      -- fork1    <- gen_lam e l d k t1 s1 f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      gen_lam_all e l d k t_wnf s f r b c
    t' -> do
      gen_body e l d k t' s f r b c

-- def Term/gen/lam/all(...) -> Term:
gen_lam_all :: Gen Term
gen_lam_all e l d k t s f r b c = do
  -- In Bend, this function checks if A is frozen. We skip that distinction here.
  gen_lam_all_try e l d k t s f r b c

-- def Term/gen/lam/all/try(...) -> Term:
gen_lam_all_try :: Gen Term
gen_lam_all_try e l d k t s f r b c = do
  if k == 0 then do
    gen_lam_var e l d 0 t s f r b c
  else do
    (t0, t1) <- clone e l t
    (s0, s1) <- clone e l s
    (f0, f1) <- clone_list e l f
    (r0, r1) <- clone_pair e l r
    (b0, b1) <- clone_pair_list e l b
    (c0, c1) <- clone_pair_list e l c
    fork0    <- gen_lam_var e (sp0 l) d k     t0 s0 f0 r0 b0 c0
    fork1    <- gen_lam_mat e (sp1 l) d (k-1) t1 s1 f1 r1 b1 c1
    return $ Sup l fork0 fork1

-- def Term/gen/lam/var(...) -> Term:
gen_lam_var :: Gen Term
gen_lam_var e l d k t s f r b c = do
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (s0, s1) <- clone   e tl s
      -- (f0, f1) <- clone_list  e tl f
      -- (r0, r1) <- clone_pair  e tl r
      -- (b0, b1) <- clone_pair_list e tl b
      -- (c0, c1) <- clone_pair_list e tl c
      -- fork0    <- gen_lam_var e l d k t0 s0 f0 r0 b0 c0
      -- fork1    <- gen_lam_var e l d k t1 s1 f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    (All ta tb) -> do
      x  <- fresh e
      xv <- return $ Nam (int_to_name d)
      s' <- return $ App s xv
      f' <- gen_fol_arg e f xv
      c' <- return $ c ++ [(xv, ta)]
      t' <- return $ App tb xv
      fn <- gen_lam e l (d + 1) k t' s' f' r b c'
      return $ Lam x fn
    _ -> do
      return Era -- Cannot introduce lambda if type is not All.

gen_lam_mat :: Gen Term
gen_lam_mat e l d k t s f r b c = do
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (s0, s1) <- clone   e tl s
      -- (f0, f1) <- clone_list  e tl f
      -- (r0, r1) <- clone_pair  e tl r
      -- (b0, b1) <- clone_pair_list e tl b
      -- (c0, c1) <- clone_pair_list e tl c
      -- fork0    <- gen_lam_mat e l d k t0 s0 f0 r0 b0 c0
      -- fork1    <- gen_lam_mat e l d k t1 s1 f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      !a_wnf <- wnf e [] ta
      case a_wnf of
        Era -> do
          return Era
        Sup tl a0 a1 -> do
          error "TODO"
          -- (s0, s1)   <- clone   e tl s
          -- (f0, f1)   <- clone_list  e tl f
          -- (r0, r1)   <- clone_pair  e tl r
          -- (b0, b1)   <- clone_pair_list e tl b
          -- (c0, c1)   <- clone_pair_list e tl c
          -- (tb0, tb1) <- clone   e tl tb
          -- fork0      <- gen_lam_mat e l d k (All a0 tb0) s0 f0 r0 b0 c0
          -- fork1      <- gen_lam_mat e l d k (All a1 tb1) s1 f1 r1 b1 c1
          -- return $ Sup tl fork0 fork1
        Nat -> do
          -- clone_list due to truly duplicated usage (not a fork)
          (tb0, tb1) <- clone e 0 tb
          (s0, s1)   <- clone e 0 s
          (f0, f1)   <- clone_list e 0 f
          (r0, r1)   <- clone_pair e 0 r
          (b0, b1)   <- clone_pair_list e 0 b
          (c0, c1)   <- clone_pair_list e 0 c
          n          <- fresh e
          m          <- fresh e
          p          <- fresh e
          z_t        <- return $ App tb0 Zer
          z_s        <- return $ App s0 Zer
          z_f        <- gen_fol_arg e f0 Zer
          z_x        <- gen_lam e (sp0 l) d k z_t z_s z_f r0 b0 c0
          s_t        <- return $ All Nat (Lam n (App tb1 (Suc (Var n))))
          s_s        <- return $ App s1 (Lam m (Suc (Var m)))
          s_f        <- return $ App s1 (Lam p (Var p)) : f1
          s_x        <- gen_lam e (sp1 l) d k s_t s_s s_f r1 b1 c1
          return $ Swi z_x s_x
        _ -> do -- Cannot match on this argument type.
          return Era
    _ -> do -- Cannot match if type is not All.
      return Era

-- def Term/gen/body(...) -> Term:
gen_body :: Gen Term
gen_body e l d k t s f r b c = do
  gen_expr e l d max_intr t s f r b c

-- Enumerator (RHS)
-- ----------------

-- def Term/gen/expr(...) -> Term:
gen_expr :: Gen Term
gen_expr e l d k t s f r b c = do
  if k == 0 then do
    return Zer
    -- gen_pick e l d 0 t s f r b c
  else do
    (t0, t1) <- clone e l t
    (s0, s1) <- clone e l s
    (f0, f1) <- clone_list e l f
    (r0, r1) <- clone_pair e l r
    (b0, b1) <- clone_pair_list e l b
    (c0, c1) <- clone_pair_list e l c
    fork0    <- gen_intr e (sp0 l) d (k-1) t0 s0 f0 r0 b0 c0
    -- fork0    <- return $ Zer
    fork1    <- gen_pick e (sp1 l) d k t1 s1 f1 r1 b1 c1
    -- fork1    <- return $ Zer
    return $ Sup l fork0 fork1

-- Introduce Constructor
-- ---------------------

-- def Term/gen/intr(...) -> Term:
gen_intr :: Gen Term
gen_intr e l d k t s f r b c = do
  !t_wnf <- wnf e [] t
  case t_wnf of
    Era -> do
      return Era
    Sup tl t0 t1 -> do
      error "TODO"
      -- (s0, s1) <- clone e tl s
      -- (f0, f1) <- clone_list e tl f
      -- (r0, r1) <- clone_pair e tl r
      -- (b0, b1) <- clone_pair_list e tl b
      -- (c0, c1) <- clone_pair_list e tl c
      -- fork0    <- gen_intr e l d k t0 s0 f0 r0 b0 c0
      -- fork1    <- gen_intr e l d k t1 s1 f1 r1 b1 c1
      -- return $ Sup tl fork0 fork1
    Nat -> do
      (s0, s1) <- clone e l s
      (f0, f1) <- clone_list e l f
      (r0, r1) <- clone_pair e l r
      (b0, b1) <- clone_pair_list e l b
      (c0, c1) <- clone_pair_list e l c
      fork0    <- return $ Zer
      pred     <- gen_expr e (sp1 l) d k Nat s1 f1 r1 b1 c1
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
      (t0, t1)   <- clone e l t
      (s0, s1)   <- clone e l s
      (f0, f1)   <- clone_list e l f
      (r0, r1)   <- clone_pair e l r
      (c0, c1)   <- clone_pair_list e l c
      (bs0, bs1) <- clone_pair_list e l bs
      fork0      <- gen_call e (sp0 l) d k t0 s0 f0 r0 bs0 c0 tm ty
      fork1      <- gen_pick_lib e (sp1 l) d k t1 s1 f1 r1 bs1 c1
      return $ Sup l fork0 fork1

gen_pick_fol :: Gen Term
gen_pick_fol e l d k t s f r b c = do
  case f of
    [] -> do
      gen_pick_ctx e l d k t s [] r b c
    (rxs : fs) -> do
      (t0, t1)     <- clone e l t
      (s0, s1)     <- clone e l s
      (b0, b1)     <- clone_pair_list e l b
      (c0, c1)     <- clone_pair_list e l c
      (r0, r1)     <- clone_pair e l r
      (fs0, fs1)   <- clone_list e l fs
      (tm0, ty0)   <- return $ r0
      (tm0A, tm0B) <- clone e l tm0
      (ty0A, ty0B) <- clone e l ty0
      fork0        <- gen_fold e (sp0 l) d k t0 s0 [] (tm0A,ty0A) b0 c0 (lhs_to_list rxs) tm0B ty0B
      fork1        <- gen_pick_fol e (sp1 l) d k t1 s1 fs1 r1 b1 c1
      return $ Sup l fork0 fork1

gen_pick_ctx :: Gen Term
gen_pick_ctx e l d k t s f r b c = do
  case c of
    [] -> do
      return Era
    [(tm, ty)] -> do
      gen_call e l d k t s f r b [] tm ty
    ((tm, ty) : cs) -> do
      (t0, t1)   <- clone e l t
      (s0, s1)   <- clone e l s
      (f0, f1)   <- clone_list e l f
      (r0, r1)   <- clone_pair e l r
      (b0, b1)   <- clone_pair_list e l b
      (cs0, cs1) <- clone_pair_list e l cs
      fork0      <- gen_call e (sp0 l) d k t0 s0 f0 r0 b0 cs0 tm ty
      fork1      <- gen_pick_ctx e (sp1 l) d k t1 s1 f1 r1 b1 cs1
      return $ Sup l fork0 fork1

-- Callers
-- -------

-- def Term/gen/fold(...) -> Term:
gen_fold :: Env -> Int -> Int -> Int -> Term -> Term -> [Term] -> Ann -> [Ann] -> [Ann] -> [Term] -> Term -> Term -> IO Term
gen_fold e l d k t s f r b c args tm ty = do
  case args of
    [] -> do
      gen_call e l d rec_intr t s f r b c tm ty
    (arg : args_rest) -> do
      case ty of
        All ta tb -> do
          let tm' = App tm arg
          let ty' = App tb arg
          gen_fold e l d k t s f r b c args_rest tm' ty'
        _ -> do
          return Era -- Type mismatch: expected All type.

gen_call :: Env -> Int -> Int -> Int -> Term -> Term -> [Term] -> Ann -> [Ann] -> [Ann] -> Term -> Term -> IO Term
gen_call e l d k t s f r b c tm ty = do
  !ty_wnf <- wnf e [] ty
  case ty_wnf of
    Era -> do
      return Era
    Sup tl ty0 ty1 -> do
      error "TODO"
      -- (t0, t1)   <- clone e tl t
      -- (s0, s1)   <- clone e tl s
      -- (f0, f1)   <- clone_list e tl f
      -- (r0, r1)   <- clone_pair e tl r
      -- (b0, b1)   <- clone_pair_list e tl b
      -- (c0, c1)   <- clone_pair_list e tl c
      -- (tm0, tm1) <- clone   e tl tm
      -- fork0      <- gen_call e l d k t0 s0 f0 r0 b0 c0 tm0 ty0
      -- fork1      <- gen_call e l d k t1 s1 f1 r1 b1 c1 tm1 ty1
      -- return $ Sup tl fork0 fork1
    All ta tb -> do
      (s0, s1) <- clone e l s
      (f0, f1) <- clone_list e l f
      (r0, r1) <- clone_pair e l r
      (b0, b1) <- clone_pair_list e l b
      (c0, c1) <- clone_pair_list e l c
      arg      <- gen_expr e (sp0 l) d k ta s0 f0 r0 b0 c0
      let tm'  = App tm arg
      let ty'  = App tb arg
      fun <- gen_call e (sp1 l) d k t s1 f1 r1 b1 c1 tm' ty'
      return fun
    _ -> do
      !t_wnf   <- wnf e [] t
      !ty_norm <- snf e d ty_wnf
      !t_norm  <- snf e d t_wnf
      if ty_norm == t_norm then
        return tm
      else
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
  [ ("(@not 0)", "1")
  , ("(@not 1+0)", "0")
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(@and 0 a)")
  , ("λx.(@and x 0)", "λa.(@and a 0)")
  , ("(@sum 1+1+1+0)", "6")
  , ("λx.(@sum 1+1+1+x)", "λa.3+(@add a 2+(@add a 1+(@add a (@sum a))))")
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
  , ("@gen", "&A{&B{λa.a,λa.1+a},&C{&D{λ{0:0;1+:λa.(@gen a)},&E{λ{0:0;1+:λa.1+(@gen a)},λ{0:0;1+:λa.2+(@gen a)}}},&D{λ{0:1;1+:λa.(@gen a)},&E{λ{0:1;1+:λa.1+(@gen a)},λ{0:1;1+:λa.2+(@gen a)}}}}}")
  , ("λx.(@gen 2+x)", "&A{&B{λa.2+a,λa.3+a},&D{λa.(@gen a),&E{λa.2+(@gen a),λa.4+(@gen a)}}}")
  , ("(@gen 2)", "&A{&B{2,3},&D{&C{0,1},&E{&C{2,3},&C{4,5}}}}")
  ]

book :: String
book = unlines
  [ "@id  = λa.a"
  , "@not = λ{0:1+0;1+:λp.0}"
  , "@dbl = λ{0:0;1+:λp.1+1+(@dbl p)}"
  , "@and = λ{0:λ{0:0;1+:λp.0};1+:λp.λ{0:0;1+:λp.1+0}}"
  , "@add = λ{0:λb.b;1+:λa.λb.1+(@add a b)}"
  , "@sum = λ{0:0;1+:λp.!P&S=p;1+(@add P₀ (@sum P₁))}"
  , "@foo = &L{λx.x,λ{0:0;1+:λp.p}}"
  , "@gen = !F&A=@gen &A{λx.!X&B=x;&B{X₀,1+X₁},λ{0:&C{0,1};1+:λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  ]

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

test :: IO ()
test = forM_ tests $ \ (src, exp) -> do
  env <- new_env $ read_book book
  det <- collapse env $ read_term src
  det <- show <$> snf env 1 det
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " → " ++ det
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = test

-- main = do
  -- !env <- new_env $ read_book book
  -- -- !val <- gen_lam env 1 0 max_elim (All Nat (Lam 0 Nat)) (Lam 0 (Var 0)) [] (Nam "F", (All Nat (Lam 0 Nat))) [] []
  -- !val <- alloc env $ read_term "@gen"
  -- !val <- collapse env val
  -- !val <- snf env 1 val
  -- -- !val <- return $ flatten val
  -- -- print $ val
  -- forM_ [val] print

  -- -- -- Print duplications map
  -- -- !dup_map <- readIORef (env_dup_map env)
  -- -- putStrLn $ show_dup_map dup_map
  
  -- -- -- Print substitutions map
  -- -- !sub_map <- readIORef (env_sub_map env)
  -- -- putStrLn $ show_sub_map sub_map
