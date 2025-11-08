{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

-- Import necessary standard libraries
import Control.Monad (replicateM)
import Data.Bits (shiftL)
import Data.Char (chr, ord)
import Data.IORef
import Data.List (foldl')
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM

-- Internal representation (Int-based for speed)
-- ==============================================

type Lab  = Int
type Name = Int

-- Simplified Term type. We use a "depth-as-ID" strategy during normalization (nf).
data Term
  = Var {-# UNPACK #-} !Name
  | Dp0 {-# UNPACK #-} !Name
  | Dp1 {-# UNPACK #-} !Name
  | Era
  | Sup {-# UNPACK #-} !Lab !Term !Term
  | Dup {-# UNPACK #-} !Name {-# UNPACK #-} !Lab !Term !Term
  | Lam {-# UNPACK #-} !Name !Term
  | Dry !Term !Term -- Stuck application
  | App !Term !Term

-- Configuration
-- =============

-- Namespace separation. We assume user-provided names are short (<= 4 chars).
-- 64^4 = 16777216. Parsed IDs (Base-64) are below this boundary.
freshIdStart :: Int
freshIdStart = 16777216

-- Name Encoding/Decoding
-- =================================================

-- 1. Base-64 encoding (for parsing user names/labels)
-- Alphabet: _ (0), a-z (1-26), A-Z (27-52), 0-9 (53-62), $ (63).
alphabet :: String
alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

charMap :: M.Map Char Int
charMap = M.fromList (zip alphabet [0..])

-- Assumes character is valid (checked by parser).
unsafeCharToInt :: Char -> Int
unsafeCharToInt c = charMap M.! c

-- Optimized nameToInt using strict foldl' and bit shifts (64 = 2^6).
nameToInt :: String -> Int
nameToInt = foldl' go 0
  where
    go acc c = (acc `shiftL` 6) + unsafeCharToInt c

-- Decoding Int -> Label Name (for printing labels)
intToLabName :: Int -> String
intToLabName 0 = "_"
intToLabName n = reverse $ go n
  where
    go 0 = ""
    go m = let (q, r) = m `divMod` 64
           in alphabet !! r : go q

-- 2. Base-26 Bijective (for canonical variable names: a-z during normalization)
-- 0 -> a, 1 -> b, ..., 25 -> z, 26 -> aa, ...
intToName :: Int -> String
intToName n = reverse $ go (n + 1)
  where
    go 0 = ""
    go m = let (q, r) = (m - 1) `divMod` 26
               c      = chr (ord 'a' + r)
           in c : go q

-- Parsing (Simplified and Idiomatic)
-- ===================================================================

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

-- Ensure names conform to the Base-64 alphabet
parse_nam :: ReadP String
parse_nam = lexeme $ munch1 (`M.member` charMap)

parse_term :: ReadP Term
parse_term = lexeme $ choice
  [ parse_lam, parse_dup, parse_app, parse_sup, parse_era, parse_var ]

-- Idiomatic application parsing: (t1 t2 t3 ...)
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
  return (Lam (nameToInt k) body)

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
  return (Dup (nameToInt k) (nameToInt l) v t)

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_term
    lexeme (char ',')
    b <- parse_term
    return (Sup (nameToInt l) a b)

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_var :: ReadP Term
parse_var = do
  k <- parse_nam
  let kid = nameToInt k
  choice
    [ string "₀"  >> return (Dp0 kid)
    , string "₁"  >> return (Dp1 kid)
    , return (Var kid)
    ]

read_term :: String -> Term
read_term s = case readP_to_S (parse_term <* skipSpaces <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse"

-- Environment
-- ===================================================

data Env = Env
  { inters       :: !(IORef Int)
  , id_new       :: !(IORef Int)
  , var_map      :: !(IORef (IM.IntMap Term))
  , dp0_map      :: !(IORef (IM.IntMap Term))
  , dp1_map      :: !(IORef (IM.IntMap Term))
  , dup_map_term :: !(IORef (IM.IntMap Term))
  , dup_map_lab  :: !(IORef (IM.IntMap Lab))
  }

-- Initialize environment, starting the ID counter from freshIdStart.
newEnv :: IO Env
newEnv = do
  i <- newIORef 0
  idn <- newIORef freshIdStart
  vm  <- newIORef IM.empty
  d0m <- newIORef IM.empty
  d1m <- newIORef IM.empty
  dmt <- newIORef IM.empty
  dml <- newIORef IM.empty
  return $ Env i idn vm d0m d1m dmt dml

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (inters e)
  writeIORef (inters e) (n + 1)
{-# INLINE inc_inters #-}

-- Generates a fresh ID.
fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (id_new e)
  writeIORef (id_new e) (n + 1)
  return n
{-# INLINE fresh #-}

subst_var :: Env -> Name -> Term -> IO ()
subst_var e k v = modifyIORef' (var_map e) (IM.insert k v)
{-# INLINE subst_var #-}

subst_dp0 :: Env -> Name -> Term -> IO ()
subst_dp0 e k v = modifyIORef' (dp0_map e) (IM.insert k v)
{-# INLINE subst_dp0 #-}

subst_dp1 :: Env -> Name -> Term -> IO ()
subst_dp1 e k v = modifyIORef' (dp1_map e) (IM.insert k v)
{-# INLINE subst_dp1 #-}

delay_dup :: Env -> Name -> Lab -> Term -> IO ()
delay_dup e k l v = do
  modifyIORef' (dup_map_term e) (IM.insert k v)
  modifyIORef' (dup_map_lab e) (IM.insert k l)
{-# INLINE delay_dup #-}

-- Efficiently takes a term from an IntMap, removing it.
taker_term :: IORef (IM.IntMap Term) -> Name -> IO (Maybe Term)
taker_term ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> return Nothing
    Just v -> do
      -- Clear the slot after taking (enforcing linearity/affinity)
      writeIORef ref (IM.delete k m)
      return (Just v)
{-# INLINE taker_term #-}

take_var :: Env -> Name -> IO (Maybe Term)
take_var e = taker_term (var_map e)
{-# INLINE take_var #-}

take_dp0 :: Env -> Name -> IO (Maybe Term)
take_dp0 e = taker_term (dp0_map e)
{-# INLINE take_dp0 #-}

take_dp1 :: Env -> Name -> IO (Maybe Term)
take_dp1 e = taker_term (dp1_map e)
{-# INLINE take_dp1 #-}

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = do
  !mt <- readIORef (dup_map_term e)
  case IM.lookup k mt of
    Nothing -> return Nothing
    Just v -> do
      !ml <- readIORef (dup_map_lab e)
      writeIORef (dup_map_term e) (IM.delete k mt)
      writeIORef (dup_map_lab e) (IM.delete k ml)
      case IM.lookup k ml of
        Just l  -> return (Just (l, v))
        Nothing -> return Nothing
{-# INLINE take_dup #-}

-- Evaluation (Weak Head Normal Form)
-- ==================================

wnf :: Env -> Term -> IO Term
wnf e (App f x) = do
  !f0 <- wnf e f
  app e f0 x
wnf e (Dup k l v t) = do
  delay_dup e k l v
  wnf e t
wnf e (Var x) = var e x
wnf e (Dp0 x) = dp0 e x
wnf e (Dp1 x) = dp1 e x
wnf e f = return f
{-# INLINE wnf #-}

app :: Env -> Term -> Term -> IO Term
app e (Lam fk ff)   x = app_lam e fk ff x
app e (Sup fl fa fb) x = app_sup e fl fa fb x
app e (Dry df dx)   x = app_dry e df dx x
app e f             x = return $ App f x
{-# INLINE app #-}

dup :: Env -> Name -> Lab -> Term -> Term -> IO Term
dup e k l (Lam vk vf)   t = dup_lam e k l vk vf t
dup e k l (Sup vl va vb) t = dup_sup e k l vl va vb t
dup e k l (Dry vf vx)   t = dup_dry e k l vf vx t
dup e k l v             t = return $ Dup k l v t
{-# INLINE dup #-}

app_lam :: Env -> Name -> Term -> Term -> IO Term
app_lam e fx ff v = do
  inc_inters e
  subst_var e fx v
  wnf e ff
{-# INLINE app_lam #-}

app_sup :: Env -> Lab -> Term -> Term -> Term -> IO Term
app_sup e fL fa fb v = do
  inc_inters e
  x <- fresh e
  delay_dup e x fL v
  wnf e (Sup fL (App fa (Dp0 x)) (App fb (Dp1 x)))
{-# INLINE app_sup #-}

-- Stuck applications accumulate.
app_dry :: Env -> Term -> Term -> Term -> IO Term
app_dry e df dx v = do
  inc_inters e
  return $ Dry (Dry df dx) v
{-# INLINE app_dry #-}

dup_lam :: Env -> Name -> Lab -> Name -> Term -> Term -> IO Term
dup_lam e k l vk vf t = do
  inc_inters e
  x0 <- fresh e
  x1 <- fresh e
  g  <- fresh e
  subst_dp0 e k (Lam x0 (Dp0 g))
  subst_dp1 e k (Lam x1 (Dp1 g))
  subst_var e vk (Sup l (Var x0) (Var x1))
  delay_dup e g l vf
  wnf e t
{-# INLINE dup_lam #-}

dup_sup :: Env -> Name -> Lab -> Lab -> Term -> Term -> Term -> IO Term
dup_sup e k l vl va vb t
  | l == vl = do
      inc_inters e
      subst_dp0 e k va
      subst_dp1 e k vb
      wnf e t
  | otherwise = do
      inc_inters e
      a <- fresh e
      b <- fresh e
      subst_dp0 e k (Sup vl (Dp0 a) (Dp0 b))
      subst_dp1 e k (Sup vl (Dp1 a) (Dp1 b))
      delay_dup e a l va
      delay_dup e b l vb
      wnf e t
{-# INLINE dup_sup #-}

dup_dry :: Env -> Name -> Lab -> Term -> Term -> Term -> IO Term
dup_dry e k l vf vx t = do
  inc_inters e
  f <- fresh e
  x <- fresh e
  subst_dp0 e k (Dry (Dp0 f) (Dp0 x))
  subst_dp1 e k (Dry (Dp1 f) (Dp1 x))
  delay_dup e f l vf
  delay_dup e x l vx
  wnf e t
{-# INLINE dup_dry #-}

var :: Env -> Name -> IO Term
var e k = do
  mt <- take_var e k
  case mt of
    Just t  -> wnf e t
    Nothing -> return $ Var k
{-# INLINE var #-}

dp_common :: (Env -> Name -> IO (Maybe Term)) -> (Name -> Term) -> Env -> Name -> IO Term
dp_common take_dp constructor e k = do
  mt <- take_dp e k
  case mt of
    Just t  -> wnf e t
    Nothing -> do
      mlv <- take_dup e k
      case mlv of
        Just (l, v) -> do
          !v0 <- wnf e v
          dup e k l v0 (constructor k)
        Nothing -> return $ constructor k
{-# INLINE dp_common #-}

dp0 :: Env -> Name -> IO Term
dp0 = dp_common take_dp0 Dp0
{-# INLINE dp0 #-}

dp1 :: Env -> Name -> IO Term
dp1 = dp_common take_dp1 Dp1
{-# INLINE dp1 #-}

-- Normalization (Readback) (Elegant and Simplified)
-- ========================

-- Normalization function with depth counter 'd'.
-- Implements the "depth-as-ID" strategy. We substitute the bound variable (k)
-- by the current depth (d) in the environment, and update the binder (Lam/Dup)
-- in the resulting term to use 'd' as its ID.
nf :: Env -> Int -> Term -> IO Term
nf e d x = do
  !x0 <- wnf e x
  go e d x0
  where go :: Env -> Int -> Term -> IO Term
        go e d (Var k)      = return $ Var k
        go e d (Dp0 k)      = return $ Dp0 k
        go e d (Dp1 k)      = return $ Dp1 k
        go e d Era          = return Era
        go e d (Dry f x)    = Dry <$> nf e d f <*> nf e d x
        go e d (App f x)    = App <$> nf e d f <*> nf e d x
        go e d (Sup l a b)  = Sup l <$> nf e d a <*> nf e d b
        go e d (Lam k f)    = do
          let d' = d + 1
          let vec = var_map e
          -- Save, Substitute (k -> Var d), Normalize, Restore (Inlined bracket pattern)
          !m <- readIORef vec
          let !old_v = IM.lookup k m
          writeIORef vec (IM.insert k (Var d) m)
          !f0 <- nf e d' f
          !m' <- readIORef vec
          case old_v of
            Just ov -> writeIORef vec (IM.insert k ov m')
            Nothing -> writeIORef vec (IM.delete k m')
          -- Return Lam with depth 'd' as the new ID
          return $ Lam d f0
        -- Dup case: Substitute Dp0/Dp1 'k' by Dp0/Dp1 'd', normalize body, restore env, return 'Dup d ...'.
        go e d (Dup k l v t)= do
          !v0 <- nf e d v
          let d' = d + 1
          -- Substitute Dp0 (k -> Dp0 d) and save old value
          let vec0 = dp0_map e
          !m0 <- readIORef vec0
          let !old_v0 = IM.lookup k m0
          writeIORef vec0 (IM.insert k (Dp0 d) m0)
          -- Substitute Dp1 (k -> Dp1 d) and save old value
          let vec1 = dp1_map e
          !m1 <- readIORef vec1
          let !old_v1 = IM.lookup k m1
          writeIORef vec1 (IM.insert k (Dp1 d) m1)
          -- Normalize t
          !t0 <- nf e d' t
          -- Restore
          !m0' <- readIORef vec0
          case old_v0 of
            Just ov0 -> writeIORef vec0 (IM.insert k ov0 m0')
            Nothing -> writeIORef vec0 (IM.delete k m0')
          !m1' <- readIORef vec1
          case old_v1 of
            Just ov1 -> writeIORef vec1 (IM.insert k ov1 m1')
            Nothing -> writeIORef vec1 (IM.delete k m1')
          -- Return Dup with depth 'd' as the new ID
          return $ Dup d l v0 t0

-- Showing (Simplified)
-- =======

-- Simplified showTerm. No depth parameter needed.
-- Relies on the fact that IDs (k) in the normalized term are the canonical depths.
showTerm :: Term -> String
showTerm = go where
  go (Var k)       = intToName k
  go (Dp0 k)       = intToName k ++ "₀"
  go (Dp1 k)       = intToName k ++ "₁"
  go Era           = "&{}"
  -- Labels are shown using Base-64 decoding
  go (Sup l a b)   = "&" ++ intToLabName l ++ "{" ++ go a ++ "," ++ go b ++ "}"
  -- Binders use the ID stored (which is the canonical depth)
  go (Dup k l v t) = "!" ++ intToName k ++ "&" ++ intToLabName l ++ "=" ++ go v ++ ";" ++ go t
  go (Lam k f)     = "λ" ++ intToName k ++ "." ++ go f
  go (Dry f x)     = "(" ++ go f ++ " " ++ go x ++ ")"
  go (App f x)     = "(" ++ go f ++ " " ++ go x ++ ")"

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
  -- Benchmark configuration: 2^22
  let n = 22
  -- The term applies (2^22) to the 'False' church numeral (λT.λF.F), resulting in 'True' (λT.λF.T).
  let termStr = "((" ++ f n ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"

  -- Parse directly to Term.
  let term = read_term termStr

  -- Setup environment (fresh IDs start automatically at freshIdStart).
  env <- newEnv

  -- Execution
  start <- getCPUTime
  !res <- nf env 0 term -- Start normalization with depth 0
  end <- getCPUTime

  -- Output
  interactions <- readIORef (inters env)
  let diff = fromIntegral (end - start) / (10^12)
  let rate = fromIntegral interactions / diff

  -- Expected output: λa.λb.a (Canonical representation of Church True)
  putStrLn (showTerm res)
  print interactions
  printf "Time: %.3f seconds\n" (diff :: Double)
  printf "Rate: %.2f M interactions/s\n" (rate / 1000000 :: Double)
