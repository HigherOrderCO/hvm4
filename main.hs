-- The Interaction Calculus
-- ========================
-- A term rewrite system for the following language:
-- 
-- Term ::=
-- | Var ::= Name
-- | Dp0 ::= Name "₀"
-- | Dp1 ::= Name "₁"
-- | Ref ::= "@" Name
-- | Era ::= "&{}"
-- | Sup ::= "&" Name "{" Term "," Term "}"
-- | Dup ::= "!" Name "&" Name "=" Term ";" Term
-- | Lam ::= "λ" Name "." Term
-- | App ::= "(" Term " " Term ")"
-- | Bt0 ::= "#0"
-- | Bt1 ::= "#1"
-- | Zer ::= "0"
-- | Suc ::= "1+"
-- | Nil ::= "[]"
-- | Con ::= Term "<>" Term
--
-- Where:
-- 
-- Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $
-- 
-- In it, variables are affine (they must occur at most once), and range
-- globally (they can occur "outside" of their binder's "body").
-- 
-- Functions can be defined as:
-- 
-- Func ::= "@" Name "=" CaseTree
-- 
-- Where a CaseTree can be defined as:
-- 
-- CaseTree ::=
-- | CLam ::= "Λ" Name "." Case
-- | CTup ::= "Λ" "{" "#(,)" ":" Case ";"? "}"
-- | CBit ::= "Λ" "{" "#0" ":" Case ";"? "#1" ":" Case ";"? "}"
-- | CNat ::= "Λ" "{" "0" ":" Case ";"? "1+" ":" Case ";"? "}"
-- | CLst ::= "Λ" "{" "[]" ":" Case ";"? "<>" ":" Case ";"? "}"
-- | CRet ::= Term
-- 
-- Terms are rewritten via the following interaction rules:
-- 
-- (λx.f a)
-- -------- app-lam
-- x ← a
-- f
-- 
-- (&L{f,g} a)
-- ----------------- app-sup
-- ! A &L = a
-- &L{(f A₀),(g A₁)}
-- 
-- ! F &L = λx.f
-- ------------- dup-lam
-- F₀ ← λ$x0.G₀
-- F₁ ← λ$x1.G₁
-- x  ← &L{$x0,$x1}
-- ! G &L = f
-- 
-- ! X &L = &R{a,b}
-- ---------------- dup-sup
-- if L == R:
--   X₀ ← a
--   X₁ ← b
-- else:
--   ! A &L = a
--   ! B &L = b
--   X₀ ← &R{A₀,B₀}
--   X₁ ← &R{A₁,B₁}
-- 
-- References are applied using the match interactions:
-- 
-- match Λx.f (a):S
-- ---------------- match-any
-- x ← a
-- match f S
-- 
-- match Λ{#(,):t} ((x,y):S)
-- ------------------------- match-sig-tup
-- match t (x:y:S)
-- 
-- match Λ{#0:f;#1:t} (#0:S)
-- ------------------------- match-bit-bt0
-- match f S
-- 
-- match Λ{#0:f;#1:t} (#0:S)
-- ------------------------- match-bit-bt1
-- match t S
-- 
-- match Λ{0:z;1+:s} (0:S)
-- ----------------------- match-nat-zer
-- match z S
-- 
-- match Λ{0:z;1+:s} (1+n:S)
-- ------------------------- match-nat-suc
-- match n (n:S)
-- 
-- match Λ{[]:n;<>:c} ([]:S)
-- ------------------------- match-lst-nil
-- match n S
-- 
-- match Λ{[]:n;<>:c} (x<>xs:S)
-- ---------------------------- match-lst-con
-- match c (x:xs:S)
-- 
-- match Λ{#(,):t} (&L{a,b}:S)
-- ------------------------------ match-bit-tup
-- ! &L S = S
-- ! &L T = t
-- &L{(match Λ{#(,):T₀} a:S₀)
--    (match Λ{#(,):T₁} b:S₁)}
-- 
-- match Λ{#0:f;#1:t} (&L{a,b}:S)
-- ------------------------------ match-bit-sup
-- ! &L S = S
-- ! &L F = f
-- ! &L T = t
-- &L{(match Λ{#0:F₀;#1:T₀} a:S₀)
--    (match Λ{#0:F₁;#1:T₁} b:S₁)}
-- 
-- match Λ{0:z;1+:s} (&L{a,b}:S)
-- ------------------------------ match-nat-sup
-- ! &L S = S
-- ! &L Z = z
-- ! &L N = s
-- &L{(match Λ{0:Z₀;1+:N₀} a:S₀)
--    (match Λ{0:Z₁;1+:N₁} b:S₁)}
-- 
-- match Λ{[]:n;<>:c} (&L{a,b}:S)
-- ------------------------------ match-lst-sup
-- ! &L S = S
-- ! &L N = n
-- ! &L C = c
-- &L{(match Λ{[]:N₀;<>:C₀} a:S₀)
--    (match Λ{[]:N₁;<>:C₁} b:S₁)}
-- 
-- match t S
-- --------------- match-end
-- wnf S (alloc t)
-- 
-- Finally, the alloc operation converts a Func to a Term:
-- 
-- alloc Λx.f
-- ----------- alloc-lam
-- x ← fresh
-- λx. alloc f
-- 
-- alloc (f x)
-- --------------------- alloc-app
-- ((alloc f) (alloc x))
-- 
-- ... etc ...

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultilineStrings #-}
{-# OPTIONS_GHC -O2 #-}

import Control.Monad (replicateM, when)
import Data.Bits (shiftL)
import Data.Char (chr, ord)
import Data.IORef
import Data.List (foldl')
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

-- Types
-- =====

type Lab  = Int
type Name = Int

data Term
  = Ref !Name
  | Var !Name
  | Dp0 !Name
  | Dp1 !Name
  | Era
  | Sup !Lab !Term !Term
  | Dup !Name !Lab !Term !Term
  | Lam !Name !Term
  | App !Term !Term
  | Bt0
  | Bt1
  | Zer
  | Suc !Term
  | Nil
  | Con !Term !Term
  deriving (Eq)

data CaseTree
  = CLam !Name !CaseTree
  | CTup !CaseTree
  | CBit !CaseTree !CaseTree
  | CNat !CaseTree !CaseTree
  | CLst !CaseTree !CaseTree
  | CRet !Term

data Book = Book (M.Map Name CaseTree)

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name (k+1)
  show (Dp0 k)       = int_to_name (k+1) ++ "₀"
  show (Dp1 k)       = int_to_name (k+1) ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name (k+1) ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name (k+1) ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"

instance Show CaseTree where
  show (CLam k ct)   = "Λ" ++ int_to_name (k+1) ++ "." ++ show ct
  show (CTup ct)     = "Λ{#(,):" ++ show ct ++ "}"
  show (CBit f t)    = "Λ{#0:" ++ show f ++ ";#1:" ++ show t ++ "}"
  show (CNat z s)    = "Λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (CLst n c)    = "Λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (CRet t)      = show t

instance Show Book where
  show (Book m) = unlines [showFunc k ct | (k, ct) <- M.toList m]
    where showFunc k ct = "@" ++ int_to_name k ++ " = " ++ show ct

-- Name Encoding/Decoding
-- ======================

-- Base-64 encoding (for parsing user names/labels and printing)
-- Alphabet: _ (0), a-z (1-26), A-Z (27-52), 0-9 (53-62), $ (63).
alphabet :: String
alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

char_map :: M.Map Char Int
char_map = M.fromList (zip alphabet [0..])

name_to_int :: String -> Int
name_to_int = foldl' go 0
  where go acc c = (acc `shiftL` 6) + char_map M.! c

int_to_name :: Int -> String
int_to_name 0 = "_"
int_to_name n = reverse $ go n
  where go 0 = ""
        go m = let (q,r) = m `divMod` 64
               in alphabet !! r : go q

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

parse_nam :: ReadP String
parse_nam = lexeme $ munch1 (`M.member` char_map)

-- Two-phase term parsing to handle the "<>" operator correctly
parse_term :: ReadP Term
parse_term = do
  base <- parse_term_base
  parse_term_suff base

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam
  , parse_dup
  , parse_app
  , parse_sup
  , parse_era
  , parse_ref
  , parse_bt0
  , parse_bt1
  , parse_zer
  , parse_suc
  , parse_nil
  , parse_var
  ]

parse_term_suff :: Term -> ReadP Term
parse_term_suff base = choice
  [ do lexeme (string "<>")
       rest <- parse_term
       return (Con base rest)
  , return base
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
  lexeme (char ';')
  t <- parse_term
  return (Dup (name_to_int k) (name_to_int l) v t)

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_term
    lexeme (char ',')
    b <- parse_term
    return (Sup (name_to_int l) a b)

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_ref :: ReadP Term
parse_ref = do
  lexeme (char '@')
  k <- parse_nam
  return (Ref (name_to_int k))

parse_bt0 :: ReadP Term
parse_bt0 = lexeme (string "#0") >> return Bt0

parse_bt1 :: ReadP Term
parse_bt1 = lexeme (string "#1") >> return Bt1

parse_zer :: ReadP Term
parse_zer = lexeme (char '0') >> return Zer

parse_suc :: ReadP Term
parse_suc = do
  lexeme (string "1+")
  n <- parse_term
  return (Suc n)

parse_nil :: ReadP Term
parse_nil = lexeme (string "[]") >> return Nil

parse_var :: ReadP Term
parse_var = do
  k <- parse_nam
  let kid = name_to_int k
  choice
    [ string "₀"  >> return (Dp0 kid)
    , string "₁"  >> return (Dp1 kid)
    , return (Var kid)
    ]

-- CaseTree parsers
parse_case_tree :: ReadP CaseTree
parse_case_tree = lexeme $ choice
  [ parse_clam
  , parse_ctup
  , parse_cbit
  , parse_cnat
  , parse_clst
  , parse_cret
  ]

parse_clam :: ReadP CaseTree
parse_clam = do
  lexeme (choice [char 'Λ', char '^'])
  k <- parse_nam
  lexeme (char '.')
  body <- parse_case_tree
  return (CLam (name_to_int k) body)

parse_ctup :: ReadP CaseTree
parse_ctup = do
  lexeme (choice [char 'Λ', char '^'])
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "#(,)")
    lexeme (char ':')
    t <- parse_case_tree
    optional (lexeme (char ';'))
    return (CTup t)

parse_cbit :: ReadP CaseTree
parse_cbit = do
  lexeme (choice [char 'Λ', char '^'])
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "#0")
    lexeme (char ':')
    f <- parse_case_tree
    optional (lexeme (char ';'))
    lexeme (string "#1")
    lexeme (char ':')
    t <- parse_case_tree
    optional (lexeme (char ';'))
    return (CBit f t)

parse_cnat :: ReadP CaseTree
parse_cnat = do
  lexeme (choice [char 'Λ', char '^'])
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (char '0')
    lexeme (char ':')
    z <- parse_case_tree
    optional (lexeme (char ';'))
    lexeme (string "1+")
    lexeme (char ':')
    s <- parse_case_tree
    optional (lexeme (char ';'))
    return (CNat z s)

parse_clst :: ReadP CaseTree
parse_clst = do
  lexeme (choice [char 'Λ', char '^'])
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    lexeme (string "[]")
    lexeme (char ':')
    n <- parse_case_tree
    optional (lexeme (char ';'))
    lexeme (string "<>")
    lexeme (char ':')
    c <- parse_case_tree
    optional (lexeme (char ';'))
    return (CLst n c)

parse_cret :: ReadP CaseTree
parse_cret = CRet <$> parse_term

-- Function definition parser
parse_func :: ReadP (Name, CaseTree)
parse_func = do
  lexeme (char '@')
  k <- parse_nam
  lexeme (char '=')
  ct <- parse_case_tree
  return (name_to_int k, ct)

-- Book parser
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

data Env = Env
  { inters  :: !(IORef Int)
  , id_new  :: !(IORef Int)
  , var_map :: !(IORef (IM.IntMap Term))
  , dp0_map :: !(IORef (IM.IntMap Term))
  , dp1_map :: !(IORef (IM.IntMap Term))
  , dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

new_env :: IO Env
new_env = do
  itr <- newIORef 0
  ids <- newIORef 0
  vm  <- newIORef IM.empty
  d0m <- newIORef IM.empty
  d1m <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env itr ids vm d0m d1m dm

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (inters e)
  writeIORef (inters e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (id_new e)
  writeIORef (id_new e) (n + 1)
  return ((n `shiftL` 6) + 63)

subst_var :: Env -> Name -> Term -> IO ()
subst_var e k v = modifyIORef' (var_map e) (IM.insert k v)

subst_dp0 :: Env -> Name -> Term -> IO ()
subst_dp0 e k v = modifyIORef' (dp0_map e) (IM.insert k v)

subst_dp1 :: Env -> Name -> Term -> IO ()
subst_dp1 e k v = modifyIORef' (dp1_map e) (IM.insert k v)

delay_dup :: Env -> Name -> Lab -> Term -> IO ()
delay_dup e k l v = modifyIORef' (dup_map e) (IM.insert k (l, v))

-- Atomically takes a value from a map.
taker :: IORef (IM.IntMap a) -> Name -> IO (Maybe a)
taker ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_var :: Env -> Name -> IO (Maybe Term)
take_var e = taker (var_map e)

take_dp0 :: Env -> Name -> IO (Maybe Term)
take_dp0 e = taker (dp0_map e)

take_dp1 :: Env -> Name -> IO (Maybe Term)
take_dp1 e = taker (dp1_map e)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e = taker (dup_map e)

-- Evaluation (Weak Head Normal Form, Tail-Recursive)
-- ==================================================

data Frame
  = FApp Term        -- Stores the argument 'x' while reducing the function 'f' in (f x).
  | FDp0 Name Lab    -- Stores the context (k, l) when Dp0 k accesses a delayed dup !k &l = v.
  | FDp1 Name Lab    -- Stores the context (k, l) when Dp1 k accesses a delayed dup.

type Stack = [Frame]

-- Main WNF loop: drives reduction by analyzing the term structure.
wnf :: Env -> Stack -> Term -> IO Term
wnf e s (App f x)     = wnf e (FApp x : s) f
wnf e s (Dup k l v t) = delay_dup e k l v >> wnf e s t
wnf e s (Var k)       = wnf_var e s k
wnf e s (Dp0 k)       = wnf_dup e s k FDp0 wnf_dp0
wnf e s (Dp1 k)       = wnf_dup e s k FDp1 wnf_dp1
wnf e s f             = wnf_unwind e s f -- Reached a head form (Lam, Sup, Era).

-- Auxiliary function for handling Dp0/Dp1 in wnf: checks for delayed dup
wnf_dup :: Env -> Stack -> Name -> (Name -> Lab -> Frame) -> (Env -> Stack -> Name -> IO Term) -> IO Term
wnf_dup e s k mkFrame fallback = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf e (mkFrame k l : s) v
    Nothing     -> fallback e s k

-- wnf_unwind loop: applies the reduced term (head form) to the stack frames (context).
wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []             v = return v
wnf_unwind e (FApp x   : s) v = wnf_app e s v x
wnf_unwind e (FDp0 k l : s) v = wnf_dup_interact e s k l v (Dp0 k)
wnf_unwind e (FDp1 k l : s) v = wnf_dup_interact e s k l v (Dp1 k)

-- Variable and Port Handlers (Substitution)
-- -----------------------------------------

wnf_get_subst :: Env -> Stack -> Name -> (Env -> Name -> IO (Maybe Term)) -> (Name -> Term) -> IO Term
wnf_get_subst e s k takeFunc mkTerm = do
  mt <- takeFunc e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s (mkTerm k)

-- Var: Check for substitution in var_map.
wnf_var :: Env -> Stack -> Name -> IO Term
wnf_var e s k = wnf_get_subst e s k take_var Var

-- Dp0: Check for substitution in dp0_map.
wnf_dp0 :: Env -> Stack -> Name -> IO Term
wnf_dp0 e s k = wnf_get_subst e s k take_dp0 Dp0

-- Dp1: Check for substitution in dp1_map.
wnf_dp1 :: Env -> Stack -> Name -> IO Term
wnf_dp1 e s k = wnf_get_subst e s k take_dp1 Dp1

-- Interaction Dispatchers
-- -----------------------

-- App: Handles application interactions.
wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s (Lam fk ff)    x = wnf_app_lam e s fk ff x
wnf_app e s (Sup fl fa fb) x = wnf_app_sup e s fl fa fb x
wnf_app e s f              x = wnf_unwind e s (App f x)

-- Dup: Handles duplication interactions. 'v' is the reduced value, 't' is the continuation.
wnf_dup_interact :: Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnf_dup_interact e s k l (Lam vk vf)    t = wnf_dup_lam e s k l vk vf t
wnf_dup_interact e s k l (Sup vl va vb) t = wnf_dup_sup e s k l vl va vb t
wnf_dup_interact e s k l v              t = wnf_unwind e s (Dup k l v t)

-- Interaction Rules
-- -----------------

-- (λx.f a)
wnf_app_lam :: Env -> Stack -> Name -> Term -> Term -> IO Term
wnf_app_lam e s fx ff v = do
  inc_inters e
  subst_var e fx v
  wnf e s ff

-- (&L{f,g} a)
wnf_app_sup :: Env -> Stack -> Lab -> Term -> Term -> Term -> IO Term
wnf_app_sup e s fL fa fb v = do
  inc_inters e
  x <- fresh e
  delay_dup e x fL v
  wnf e s (Sup fL (App fa (Dp0 x)) (App fb (Dp1 x)))

-- ! F &L = λx.f
wnf_dup_lam :: Env -> Stack -> Name -> Lab -> Name -> Term -> Term -> IO Term
wnf_dup_lam e s k l vk vf t = do
  inc_inters e
  x0 <- fresh e
  x1 <- fresh e
  g  <- fresh e
  -- Populate substitution maps.
  subst_dp0 e k (Lam x0 (Dp0 g))
  subst_dp1 e k (Lam x1 (Dp1 g))
  subst_var e vk (Sup l (Var x0) (Var x1))
  delay_dup e g l vf
  -- Continue evaluation of the current side 't' (Dp0 k or Dp1 k).
  -- This will recursively call wnf, which will now find the substitution via dp0/dp1.
  wnf e s t

-- ! X &L = &R{a,b}
wnf_dup_sup :: Env -> Stack -> Name -> Lab -> Lab -> Term -> Term -> Term -> IO Term
wnf_dup_sup e s k l vl va vb t
  | l == vl = do
      inc_inters e
      -- Populate substitution maps.
      subst_dp0 e k va
      subst_dp1 e k vb
      wnf e s t
  | otherwise = do
      inc_inters e
      a <- fresh e
      b <- fresh e
      -- Populate substitution maps.
      subst_dp0 e k (Sup vl (Dp0 a) (Dp0 b))
      subst_dp1 e k (Sup vl (Dp1 a) (Dp1 b))
      delay_dup e a l va
      delay_dup e b l vb
      wnf e s t

-- Normalization
-- =============

nf :: Env -> Int -> Term -> IO Term
-- Initialize normalization by calling wnf with an empty stack [].
nf e d x = do { !x0 <- wnf e [] x ; go e d x0 } where
  go :: Env -> Int -> Term -> IO Term
  go e d (Var k) = do
    return $ Var k
  go e d (Dp0 k) = do
    return $ Dp0 k
  go e d (Dp1 k) = do
    return $ Dp1 k
  go e d Era = do
    return Era
  go e d (App f x) = do
    !f0 <- nf e d f
    !x0 <- nf e d x
    return $ App f0 x0
  go e d (Sup l a b) = do
    !a0 <- nf e d a
    !b0 <- nf e d b
    return $ Sup l a0 b0
  go e d (Lam k f) = do
    subst_var e k (Var d)
    !f0 <- nf e (d + 1) f
    return $ Lam d f0
  go e d (Dup k l v t) = do
    !v0 <- nf e d v
    subst_dp0 e k (Dp0 d)
    subst_dp1 e k (Dp1 d)
    !t0 <- nf e (d + 1) t
    return $ Dup d l v0 t0

-- Benchmark term generator
-- =========================

-- Generates the church-encoded exponentiation benchmark term.
f :: Int -> String
f n = "λf. " ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00 &A = f;\n    "
  dup i = "!F" ++ pad i ++ " &A = λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));\n    "
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

-- Main
-- ====

-- main :: IO ()
-- main = do
--   -- Benchmark configuration: 2^N
--   let n = 20
--   -- The term applies (2^N) to the 'False' church numeral (λT.λF.F), resulting in 'True' (λT.λF.T).
--   let term_str = "((" ++ f n ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"

--   -- Parse directly to Term.
--   let term = read_term term_str

--   -- Setup environment (fresh IDs start automatically at 0 and get '$' prepended).
--   env <- new_env

--   -- Execution
--   start <- getCPUTime
--   !res <- nf env 0 term -- Start normalization with depth 0
--   end <- getCPUTime

--   -- Output
--   interactions <- readIORef (inters env)
--   let diff = fromIntegral (end - start) / (10^12)
--   let rate = fromIntegral interactions / diff

--   -- Expected output: λa.λb.a (Canonical representation of Church True)
--   putStrLn (show res)
--   print interactions
--   printf "Time: %.3f seconds\n" (diff :: Double)
--   printf "Rate: %.2f M interactions/s\n" (rate / 1000000 :: Double)

-- TODO: write a new main below
-- make it parse and print a demo book
main :: IO ()
main = do
  -- Demo book following the spec:
  -- - CaseTree CLam uses Λ (capital lambda)
  -- - Term Lam uses λ (lowercase lambda)
  let book_str = """
    @id    = Λx.x
    @const = Λx.Λy.x
    @true  = Λt.Λf.t
    @false = Λt.Λf.f
    @not   = Λb.Λt.Λf.(b f t)
    @pair  = Λa.Λb.Λ{#(,):Λx.Λy.(x a b)}
    @fst   = Λp.(p λa.λb.a)
    @snd   = Λp.(p λa.λb.b)
    """

  -- Parse the book
  let book = read_book book_str

  -- Print the parsed book
  putStrLn "Parsed Book:"
  putStrLn "============"
  print book
