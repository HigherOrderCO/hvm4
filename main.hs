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
-- - Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $
-- - [T]  ::= any sequence of T separated by ","
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
-- ------------------ ref
-- foo ~> Book["foo"]
-- 
-- ((f ~> λx.g) a)
-- --------------- app-cal-lam
-- x ← a
-- (f x) ~> g
-- 
-- ((f ~> Λ{0:z;1+:s}) 0)
-- ---------------------- app-cal-swi-zer
-- (f 0) ~> z
-- 
-- ((f ~> Λ{0:z;1+:s}) 1+n)
-- ------------------------ app-cal-swi-suc
-- ((λp.(f 1+p) ~> s) n)
-- 
-- ((f ~> Λ{0:z;1+:s}) &L{a,b})
-- ---------------------------- app-cal-swi-sup
-- ! &L F = f
-- ! &L Z = z
-- ! &L N = s
-- &L{((F₀ ~> Λ{0:Z₀;1+:N₀}) a)
--   ,((F₁ ~> Λ{0:Z₁;1+:N₁}) b)}
-- 
-- ! &L X = f ~> g
-- --------------- dup-cal
-- ! &L F = f
-- ! &L G = g
-- X₀ ← F₀ ~> G₀ 
-- X₁ ← F₁ ~> G₁

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

-- Two-phase term parsing to handle the "~>" operator correctly
parse_term :: ReadP Term
parse_term = do
  base <- parse_term_base
  parse_term_suff base

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam_or_swi -- Updated to handle Lam and Swi
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
  [ do lexeme (string "~>")
       t <- parse_term
       return (Cal base t)
  , return base
  ]

parse_app :: ReadP Term
parse_app = between (lexeme (char '(')) (lexeme (char ')')) $ do
  ts <- many1 parse_term
  let (t:rest) = ts
  return (foldl' App t rest)

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  lexeme (choice [char 'λ', char '\\'])
  choice [parse_swi_body, parse_lam_body]

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
    lexeme (char ';')
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
    Nothing -> do
      return Nothing
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
  wnf_sub e s k take_var Var

wnf_enter e s (Dup k l v t) = do
  regis_dup e k l v
  wnf_enter e s t

wnf_enter e s (Dp0 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub e s k take_dp0 Dp0

wnf_enter e s (Dp1 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub e s k take_dp1 Dp1

wnf_enter e s (Ref k) = do
  let (Book m) = book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- wnf_alloc e f
      wnf_enter e s (Cal (Var k) g)
    Nothing -> do
      error $ "UndefinedReference: " ++ int_to_name k

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
    Cal f g      -> wnf_app_cal e s f g x
    f            -> wnf_unwind e s (App f x)
  FDp0 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf (Dp0 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp0 k)
    Cal f g      -> wnf_dpn_cal e s k l f g (Dp0 k)
    val          -> wnf_unwind e s (Dup k l val (Dp0 k))
  FDp1 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf (Dp1 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp1 k)
    Cal f g      -> wnf_dpn_cal e s k l f g (Dp1 k)
    val          -> wnf_unwind e s (Dup k l val (Dp1 k))

-- WNF: Interactions
-- -----------------

-- x | x₀ | x₁
wnf_sub :: Env -> Stack -> Name -> (Env -> Name -> IO (Maybe Term)) -> (Name -> Term) -> IO Term
wnf_sub e s k takeFunc mkTerm = do
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

-- ((f ~> g) a)
wnf_app_cal :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal e s f g a = do
  !g_wnf <- wnf e [] g
  case g_wnf of
    Lam fx ff -> wnf_app_cal_lam e s f fx ff a
    Swi fz fs -> wnf_app_cal_swi e s f fz fs a
    g_wnf     -> wnf_unwind e s (App (Cal f g_wnf) a)

-- ((f ~> λx.g) a)
wnf_app_cal_lam :: Env -> Stack -> Term -> Name -> Term -> Term -> IO Term
wnf_app_cal_lam e s f x g a = do
  inc_inters e
  subst_var e x a
  wnf_enter e s (Cal (App f (Var x)) g)

-- ((f ~> Λ{0:z;1+:s}) a)
wnf_app_cal_swi :: Env -> Stack -> Term -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi e s f z sc a = do
  !a_wnf <- wnf e [] a
  case a_wnf of
    Zer       -> wnf_app_cal_swi_zer e s f z
    Suc n     -> wnf_app_cal_swi_suc e s f sc n
    Sup l b c -> wnf_app_cal_swi_sup e s f z sc l b c
    a_wnf     -> wnf_unwind e s (App (Cal f (Swi z sc)) a_wnf)

-- ((f ~> Λ{0:z;1+:s}) 0)
wnf_app_cal_swi_zer :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_cal_swi_zer e s f z = do
  inc_inters e
  wnf_enter e s (Cal (App f Zer) z)

-- ((f ~> Λ{0:z;1+:s}) 1+n)
wnf_app_cal_swi_suc :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_cal_swi_suc e s f sc n = do
  inc_inters e
  p <- fresh e
  wnf_enter e s (App (Cal (Lam p (App f (Suc (Var p)))) sc) n)

-- ((f ~> Λ{0:z;1*:s}) &L{a,b})
wnf_app_cal_swi_sup :: Env -> Stack -> Term -> Term -> Term -> Lab -> Term -> Term -> IO Term
wnf_app_cal_swi_sup e s f z sc l a b = do
  inc_inters e
  f' <- fresh e
  z' <- fresh e
  s' <- fresh e
  regis_dup e f' l f
  regis_dup e z' l z
  regis_dup e s' l sc
  let swi0 = Swi (Dp0 z') (Dp0 s')
  let swi1 = Swi (Dp1 z') (Dp1 s')
  let app0 = App (Cal (Dp0 f') swi0) a
  let app1 = App (Cal (Dp1 f') swi1) b
  wnf_enter e s (Sup l app0 app1)

-- ! &L X = f ~> g
wnf_dpn_cal :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_cal e s k l f g t = do
  inc_inters e
  f' <- fresh e
  g' <- fresh e
  regis_dup e f' l f
  regis_dup e g' l g
  subst_dp0 e k (Cal (Dp0 f') (Dp0 g'))
  subst_dp1 e k (Cal (Dp1 f') (Dp1 g'))
  wnf_enter e s t

-- WNF: Alloc
-- ----------

-- Clones a term, replacing all bound names with fresh ones.
wnf_alloc :: Env -> Term -> IO Term
wnf_alloc e term = go IM.empty term where
  go :: IM.IntMap Name -> Term -> IO Term
  go m (Var k)       = return $ Var (IM.findWithDefault k k m)
  go m (Dp0 k)       = return $ Dp0 (IM.findWithDefault k k m)
  go m (Dp1 k)       = return $ Dp1 (IM.findWithDefault k k m)
  go m Era           = return Era
  go m (Sup l a b)   = Sup l <$> go m a <*> go m b
  go m (App f x)     = App <$> go m f <*> go m x
  go m Zer           = return Zer
  go m (Suc n)       = Suc <$> go m n
  go m (Swi z s)     = Swi <$> go m z <*> go m s
  go m (Ref k)       = return $ Ref k
  go m (Cal f g)     = Cal <$> go m f <*> go m g
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
  go e d Zer = do
    return Zer
  go e d (Suc n) = do
    !n0 <- nf e d n
    return $ Suc n0
  go e d (Swi z s) = do
    !z0 <- nf e d z
    !s0 <- nf e d s
    return $ Swi z0 s0
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
 let n    = 18
 let code = "((" ++ f n ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"
 let term = read_term code
 !env <- new_env (Book M.empty)
 !ini <- getCPUTime
 !res <- nf env 0 term -- Start normalization with depth 0
 !end <- getCPUTime
 !itr <- readIORef (inters env)
 let diff = fromIntegral (end - ini) / (10^12)
 let rate = fromIntegral itr / diff
 putStrLn (show res)
 print itr
 printf "Time: %.3f seconds\n" (diff :: Double)
 printf "Rate: %.2f M interactions/s\n" (rate / 1000000 :: Double)
