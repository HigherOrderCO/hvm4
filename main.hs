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
-- | Lam ::= "λ" Name "." Term
-- | App ::= "(" Term " " Term ")"
-- | Zer ::= "0"
-- | Suc ::= "1+"
-- | Ref ::= "@" Name
-- | Cal ::= Term "~>" Term
--
-- Where:
-- 
-- Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $
-- [T]  ::= any sequence of T separated by ","
-- 
-- In CoI:
-- - Variables are affine (they must occur at most once)
-- - Variables range globally (they can occur anywhere)
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
-- ---------------- dup-lam
-- F₀ ← λ$x0.G₀
-- F₁ ← λ$x1.G₁
-- x  ← &L{$x0,$x1}
-- ! G &L = f
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
-- @foo
-- ------------------- ref
-- @foo ~> Book["foo"]
-- 
-- ((f ~> λx.g) a)
-- --------------- cal-lam
-- x ← a
-- (f x) ~> g
-- 
-- ((f ~> Λ{0:z;1+:s}) 0)
-- ---------------------- cal-swi-zer
-- (f 0) ~> z
-- 
-- ((f ~> Λ{0:z;1+:s}) 1+n)
-- ------------------------ cal-swi-suc
-- ((λp.(f 1+p) ~> s) n)
-- 
-- ((f ~> Λ{0:z;1+:s}) &L{a,b})
-- ---------------------------- cal-nat-sup
-- ! &L F = f
-- ! &L Z = z
-- ! &L N = s
-- &L{(F₀~>Λ{0:Z₀;1+:N₀} a)
--   ,(F₁~>Λ{0:Z₁;1+:N₀} b)}
-- 
-- ! &L X = f ~> g
-- --------------- dup-cal
-- ! &L F = f
-- ! &L G = g
-- X₀ ← F₀ ~> G₀ 
-- X₁ ← F₁ ~> G₁
-- 
-- Stacks are cloned through the following interactions:
-- 
-- ! S &L = []
-- ----------- dup-stack-nil
-- &L{[],[]}
-- 
-- ! S &L = (_ x)<>s
-- ----------------- dup-stack-con-app
-- ! X &L = x
-- ! S &L = s
-- &L{(_ X₀)<>S₀
--   ,(_ X₁)<>S₁}
-- 
-- ! A &A = _
-- ! &L S = A₀:s
-- ------------- dup-stack-con-dup
-- if L == A:
--   error -- FIXME: reason about later
-- else:
--   ! A0 &A = _
--   ! A1 &A = _
--   A₁ ← &L{A0₁,A1₁}
--   ! &L S = s
--   &L{A0₀:S₀
--     ,A0₁:S₁}
-- 
-- @sum = λ{
--   []: 0
--   <>: λ{
--     0: λxs. (@sum xs)
--     +: λx. λxs. (@sum x<>xs)
--   } == λx.λxs.(@sum x xs)
-- } == @sum

{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

import Control.Monad (replicateM, when)
import Data.Bits (shiftL)
import Data.Char (chr, ord)
import Data.IORef
import Data.List (foldl')
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
import Unsafe.Coerce (unsafeCoerce)
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
  | Lam !Name !Term
  | App !Term !Term
  | Zer
  | Suc !Term
  | Swi !Term !Term
  | Ref !Name
  | Cal !Term !Term
  deriving (Eq)

data Book = Book (M.Map Name Term)

-- data Spine = Spine Int ([Term] -> Term)

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name (k+1)
  show (Dp0 k)       = int_to_name (k+1) ++ "₀"
  show (Dp1 k)       = int_to_name (k+1) ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name (k+1) ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name (k+1) ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"
  show Zer           = "0"
  show (Suc n)       = "1+" ++ show n
  show (Swi z s)     = "λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (Ref k)       = "@" ++ int_to_name k
  show (Cal f g)     = show f ++ "~>" ++ show g

instance Show Book where
  show (Book m) = unlines [showFunc k ct | (k, ct) <- M.toList m]
    where showFunc k ct = "@" ++ int_to_name k ++ " = " ++ show ct

-- instance Show Spine where
  -- show (Spine k f) = show (f (replicate k (Var 0)))

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
  , parse_zer
  , parse_suc
  , parse_var
  ]

parse_term_suff :: Term -> ReadP Term
parse_term_suff base = choice
  [ return base ]

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

parse_zer :: ReadP Term
parse_zer = lexeme (char '0') >> return Zer

parse_suc :: ReadP Term
parse_suc = do
  lexeme (string "1+")
  n <- parse_term
  return (Suc n)

parse_var :: ReadP Term
parse_var = do
  k <- parse_nam
  let kid = name_to_int k
  choice
    [ string "₀"  >> return (Dp0 kid)
    , string "₁"  >> return (Dp1 kid)
    , return (Var kid)
    ]

-- Function definition parser
parse_func :: ReadP (Name, Term)
parse_func = do
  lexeme (char '@')
  k <- parse_nam
  lexeme (char '=')
  f <- parse_term
  return (name_to_int k, f)

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
  { book    :: !Book
  , inters  :: !(IORef Int)
  , id_new  :: !(IORef Int)
  , var_map :: !(IORef (IM.IntMap Term))
  , dp0_map :: !(IORef (IM.IntMap Term))
  , dp1_map :: !(IORef (IM.IntMap Term))
  , dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 0
  vm  <- newIORef IM.empty
  d0m <- newIORef IM.empty
  d1m <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids vm d0m d1m dm

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (inters e)
  writeIORef (inters e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (id_new e)
  writeIORef (id_new e) (n + 1)
  return ((n `shiftL` 6) + 63)

taker :: IORef (IM.IntMap a) -> Name -> IO (Maybe a)
taker ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> return Nothing
    Just v  -> do
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

subst_var :: Env -> Name -> Term -> IO ()
subst_var e k v = modifyIORef' (var_map e) (IM.insert k v)

subst_dp0 :: Env -> Name -> Term -> IO ()
subst_dp0 e k v = modifyIORef' (dp0_map e) (IM.insert k v)

subst_dp1 :: Env -> Name -> Term -> IO ()
subst_dp1 e k v = modifyIORef' (dp1_map e) (IM.insert k v)

regis_dup :: Env -> Name -> Lab -> Term -> IO ()
regis_dup e k l v = modifyIORef' (dup_map e) (IM.insert k (l, v))

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

wnf_enter e s (App f x) = do
  wnf_enter e (FApp x : s) f

wnf_enter e s (Var k) = do
  wnf_var e s k take_var Var

wnf_enter e s (Dup k l v t) = do
  regis_dup e k l v
  wnf_enter e s t

wnf_enter e s (Dp0 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_var e s k take_dp0 Dp0

wnf_enter e s (Dp1 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_var e s k take_dp1 Dp1

wnf_enter e s (Ref k) = do
  let (Book m) = book e
  case M.lookup k m of
    Just ct -> undefined -- TODO
    Nothing -> error $ "Reference not found: " ++ int_to_name k

wnf_enter e s f = do
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []        v = return v
wnf_unwind e (frame:s) v = case frame of
  FApp x -> case v of
    Lam fk ff    -> wnf_app_lam e s fk ff x
    Sup fl fa fb -> wnf_app_sup e s fl fa fb x
    f            -> wnf_unwind e s (App f x)
  FDp0 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf (Dp0 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp0 k)
    val          -> wnf_unwind e s (Dup k l val (Dp0 k))
  FDp1 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf (Dp1 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp1 k)
    val          -> wnf_unwind e s (Dup k l val (Dp1 k))

-- WNF: Interactions
-- -----------------

-- x | x₀ | x₁
wnf_var :: Env -> Stack -> Name -> (Env -> Name -> IO (Maybe Term)) -> (Name -> Term) -> IO Term
wnf_var e s k takeFunc mkTerm = do
  mt <- takeFunc e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s (mkTerm k)

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
  regis_dup e x fL v
  wnf e s (Sup fL (App fa (Dp0 x)) (App fb (Dp1 x)))

-- ! F &L = λx.f
wnf_dpn_lam :: Env -> Stack -> Name -> Lab -> Name -> Term -> Term -> IO Term
wnf_dpn_lam e s k l vk vf t = do
  inc_inters e
  x0 <- fresh e
  x1 <- fresh e
  g  <- fresh e
  subst_dp0 e k (Lam x0 (Dp0 g))
  subst_dp1 e k (Lam x1 (Dp1 g))
  subst_var e vk (Sup l (Var x0) (Var x1))
  regis_dup e g l vf
  wnf e s t

-- ! X &L = &R{a,b}
wnf_dpn_sup :: Env -> Stack -> Name -> Lab -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_sup e s k l vl va vb t
  | l == vl = do
      inc_inters e
      subst_dp0 e k va
      subst_dp1 e k vb
      wnf e s t
  | otherwise = do
      inc_inters e
      a <- fresh e
      b <- fresh e
      subst_dp0 e k (Sup vl (Dp0 a) (Dp0 b))
      subst_dp1 e k (Sup vl (Dp1 a) (Dp1 b))
      regis_dup e a l va
      regis_dup e b l vb
      wnf e s t

-- WNF: Alloc
-- ----------

wnf_alloc = undefined -- TODO

-- WNF: Dup Stack
-- --------------

-- wnf_dup_stack :: Env -> Lab -> Stack -> IO (Stack,Stack)

-- wnf_dup_stack e l [] = do
  -- return ([], [])

-- wnf_dup_stack e l (FApp x : s) = do
  -- xk <- fresh e
  -- regis_dup e xk l x
  -- (s0, s1) <- wnf_dup_stack e l s
  -- return (FApp (Dp0 xk) : s0, FApp (Dp1 xk) : s1)

-- wnf_dup_stack e l (FDp0 ak al : s) = do
  -- if l == al
    -- then do
      -- error "dup-stack-con-dup: label clash (L == A)"
    -- else do
      -- a0 <- fresh e
      -- a1 <- fresh e
      -- subst_dp1 e ak (Sup l (Dp1 a0) (Dp1 a1))
      -- (s0, s1) <- wnf_dup_stack e l s
      -- return (FDp0 a0 al : s0, FDp0 a1 al : s1)

-- wnf_dup_stack e l _ = do
  -- undefined -- TODO

-- Normalization
-- =============

nf :: Env -> Int -> Term -> IO Term
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
  go e d Zer = return Zer
  go e d (Suc n) = do
    !n0 <- nf e d n
    return $ Suc n0
  go e d (Ref k) = do
    return $ Ref k
  go e d (Cal f g) = do
    !f0 <- nf e d f
    return f0

-- Benchmark term generator
-- =========================

-- Generates the church-encoded exponentiation benchmark term.
f :: Int -> String
f n = "λf. " ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00 &A = f;\n    "
  dup i = "!F" ++ pad i ++ " &A = λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));\n    "
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

-- Main
-- ====

main :: IO ()
main = do
 -- Benchmark configuration: 2^N
 let n = 20
 -- The term applies (2^N) to the 'False' church numeral (λT.λF.F), resulting in 'True' (λT.λF.T).
 let term_str = "((" ++ f n ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"

 -- Parse directly to Term.
 let term = read_term term_str

 -- Setup environment (fresh IDs start automatically at 0 and get '$' prepended).
 env <- new_env (Book M.empty)

 -- Execution
 start <- getCPUTime
 !res <- nf env 0 term -- Start normalization with depth 0
 end <- getCPUTime

 -- Output
 interactions <- readIORef (inters env)
 let diff = fromIntegral (end - start) / (10^12)
 let rate = fromIntegral interactions / diff

 -- Expected output: λa.λb.a (Canonical representation of Church True)
 putStrLn (show res)
 print interactions
 printf "Time: %.3f seconds\n" (diff :: Double)
 printf "Rate: %.2f M interactions/s\n" (rate / 1000000 :: Double)







-- -- -- main :: IO ()
-- -- -- main = do
  -- -- -- -- Demo book following the spec:
  -- -- -- -- - Patt CLam uses Λ (capital lambda)
  -- -- -- -- - Term Lam uses λ (lowercase lambda)
  -- -- -- let book_str = unlines
        -- -- -- [ "@id    = Λx.x"
        -- -- -- , "@const = Λx.Λy.x"
        -- -- -- , "@true  = Λt.Λf.t"
        -- -- -- , "@false = Λt.Λf.f"
        -- -- -- , "@not   = Λ{#0:#1;#1:#0}"
        -- -- -- , "@fst   = Λp.(p λa.λb.a)"
        -- -- -- , "@snd   = Λp.(p λa.λb.b)"
        -- -- -- ]

  -- -- -- -- Parse the book
  -- -- -- let book = read_book book_str

  -- -- -- -- Print the parsed book
  -- -- -- putStrLn "Parsed Book:"
  -- -- -- putStrLn "============"
  -- -- -- print book

  -- -- -- -- Test: apply @not to #0
  -- -- -- putStrLn "\nTest: (@not #0)"
  -- -- -- putStrLn "==============="
  -- -- -- let test_term = App (Ref (name_to_int "not")) Zer
  -- -- -- env <- new_env book
  -- -- -- result <- nf env 0 test_term
  -- -- -- putStrLn $ "Result: " ++ show result
