{-# LANGUAGE MultilineStrings #-}

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
-- | Swi ::= "Λ" "{" "0" ":" Term ";"? "1" "+" ":" Term ";"? "}" 
-- | Ref ::= "@" Name
-- | Cal ::= Term "~>" Term "%" Subs
--
-- Where:
-- - Subs ::= "{" [Name "→" Term] "}"
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
-- ! X &L = 0
-- ---------- dup-zer
-- X₀ ← 0
-- X₁ ← 0
-- 
-- ! X &L = 1+n
-- ------------ dup-suc
-- ! N &L = n
-- X₀ ← 1+N₀
-- X₁ ← 1+N₁
--
-- ! X &L = Λ{0:z;1+:s}
-- -------------------- dup-swi
-- ! Z &L = z
-- ! S &L = s
-- X₀ ← Λ{0:Z₀;1+:S₀}
-- X₁ ← Λ{0:Z₁;1+:S₁}
-- 
-- @foo
-- ------------------ ref
-- foo ~> Book["foo"] % {}
-- 
-- ((f ~> λx.g % m) a)
-- ------------------- app-cal-lam
-- (f x) ~> g % {m, x→a}
-- 
-- ((f ~> Λ{0:z;1+:s} % m) 0)
-- -------------------------- app-cal-swi-zer
-- (f 0) ~> z % m
-- 
-- ((f ~> Λ{0:z;1+:s} % m) 1+n)
-- ---------------------------- app-cal-swi-suc
-- ((λp.(f 1+p) ~> s % m) n)
-- 
-- ((f ~> Λ{0:z;1+:s} % m) &L{a,b})
-- -------------------------------- app-cal-swi-sup
-- ! &L F = f
-- (M₀, M₁) = dup_substs(m)
-- (Z₀, Z₁) = alloc_dup(z)
-- (S₀, S₁) = alloc_dup(s)
-- &L{((F₀ ~> Λ{0:Z₀;1+:S₀} % M₀) a)
--   ,((F₁ ~> Λ{0:Z₁;1+:S₁} % M₁) b)}
-- 
-- ! &L X = f ~> g % m
-- ------------------- dup-cal
-- ! &L F = f
-- (M₀, M₁) = dup_substs(m)
-- (G₀, G₁) = alloc_dup(g)
-- X₀ ← F₀ ~> G₀ % M₀
-- X₁ ← F₁ ~> G₁ % M₁

{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

import Control.Monad (replicateM, when, mapM)
import Data.Bits (shiftL)
import Data.Char (chr, ord)
import Data.IORef
import Data.List (foldl', intercalate, unzip)
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
  = Nam !String
  | Var !Name
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
  -- Extended Cal variant
  | Cal !Term !Term !(M.Map Name Term)
  deriving (Eq)

data Book = Book (M.Map Name Term)

-- Showing
-- =======

instance Show Term where
  show (Nam k)       = "^" ++ k
  show (Var k)       = int_to_name k
  show (Dp0 k)       = int_to_name k ++ "₀"
  show (Dp1 k)       = int_to_name k ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"
  show Zer           = "0"
  show (Suc n)       = "1+" ++ show n
  show (Swi z s)     = "Λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (Ref k)       = "@" ++ int_to_name k
  show (Cal f g m)   = show f ++ "~>" ++ show g ++ "%" ++ "{" ++ intercalate "," [int_to_name k ++ "→" ++ show v | (k, v) <- M.toList m] ++ "}"

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
parse_term_base = lexeme $
      parse_lam_or_swi
  <++ parse_dup
  <++ parse_app
  <++ parse_sup
  <++ parse_era
  <++ parse_zer
  <++ parse_suc
  <++ parse_ref
  <++ parse_var

parse_term_suff :: Term -> ReadP Term
parse_term_suff base = return base

parse_app :: ReadP Term
parse_app = between (lexeme (char '(')) (lexeme (char ')')) $ do
  ts <- many1 parse_term
  let (t:rest) = ts
  return (foldl' App t rest)

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  lexeme (choice [char 'λ', char 'Λ'])
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
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_var_map :: !(IORef (IM.IntMap Term))
  , env_dp0_map :: !(IORef (IM.IntMap Term))
  , env_dp1_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 1
  vm  <- newIORef IM.empty
  d0m <- newIORef IM.empty
  d1m <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids vm d0m d1m dm

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (env_inters e)
  writeIORef (env_inters e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (env_new_id e)
  writeIORef (env_new_id e) (n + 1)
  return n

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
take_var e = taker (env_var_map e)

take_dp0 :: Env -> Name -> IO (Maybe Term)
take_dp0 e = taker (env_dp0_map e)

take_dp1 :: Env -> Name -> IO (Maybe Term)
take_dp1 e = taker (env_dp1_map e)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e = taker (env_dup_map e)

subst_var :: Env -> Name -> Term -> IO ()
subst_var e k v = modifyIORef' (env_var_map e) (IM.insert k v)

subst_dp0 :: Env -> Name -> Term -> IO ()
subst_dp0 e k v = modifyIORef' (env_dp0_map e) (IM.insert k v)

subst_dp1 :: Env -> Name -> Term -> IO ()
subst_dp1 e k v = modifyIORef' (env_dp1_map e) (IM.insert k v)

regis_dup :: Env -> Name -> Lab -> Term -> IO ()
regis_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

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
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      -- Initialize Cal with an empty substitution map.
      putStrLn $ ">> alloc             : " ++ show f
      wnf_enter e s (Cal (Nam ("@" ++ int_to_name k)) f M.empty)
    Nothing -> do
      error $ "UndefinedReference: " ++ int_to_name k

wnf_enter e s (Cal f g m) = do
  putStrLn $ ">> wnf_enter_cal      : " ++ show (Cal f g m)
  wnf_unwind e s (Cal f g m)

wnf_enter e s f = do
  putStrLn $ ">> wnf_enter          : " ++ show f
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e [] v =
  case v of
    -- WNF evaluation semantics: Cal f g % m evaluates by allocating g using m when standalone.
    Cal f g m -> do
      g_alloc <- wnf_alloc e m g
      wnf e [] g_alloc
    f         -> return f
wnf_unwind e (frame:s) v = case frame of
  FApp x -> case v of
    Lam fk ff    -> wnf_app_lam e s fk ff x
    Sup fl fa fb -> wnf_app_sup e s fl fa fb x
    Cal f g m    -> wnf_app_cal e s f g m x
    f            -> wnf_unwind e s (App f x)
  FDp0 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf    (Dp0 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp0 k)
    Cal vf vg m  -> wnf_dpn_cal e s k l vf vg m  (Dp0 k)
    Suc vp       -> wnf_dpn_suc e s k l vp       (Dp0 k)
    Zer          -> wnf_dpn_zer e s k l          (Dp0 k)
    Swi vz vs    -> wnf_dpn_swi e s k l vz vs    (Dp0 k)
    Nam n        -> wnf_dpn_nam e s k l n        (Dp0 k)
    val          -> wnf_unwind  e s (Dup k l val (Dp0 k))
  FDp1 k l -> case v of
    Lam vk vf    -> wnf_dpn_lam e s k l vk vf    (Dp1 k)
    Sup vl va vb -> wnf_dpn_sup e s k l vl va vb (Dp1 k)
    Cal vf vg m  -> wnf_dpn_cal e s k l vf vg m  (Dp1 k)
    Suc vp       -> wnf_dpn_suc e s k l vp       (Dp1 k)
    Zer          -> wnf_dpn_zer e s k l          (Dp1 k)
    Swi vz vs    -> wnf_dpn_swi e s k l vz vs    (Dp1 k)
    Nam n        -> wnf_dpn_nam e s k l n        (Dp1 k)
    val          -> wnf_unwind  e s (Dup k l val (Dp1 k))

-- WNF: Interactions
-- -----------------

-- x | x₀ | x₁
wnf_sub :: Env -> Stack -> Name -> (Env -> Name -> IO (Maybe Term)) -> (Name -> Term) -> IO Term
wnf_sub e s k takeFunc mkTerm = do
  mt <- takeFunc e k
  case mt of
    Just t  -> wnf e s t
    -- If unbound, represent as Nam for debugging output (as seen in the trace).
    Nothing -> wnf_unwind e s (Nam (int_to_name k))

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

-- ! X &L = 0
wnf_dpn_zer :: Env -> Stack -> Name -> Lab -> Term -> IO Term
wnf_dpn_zer e s k l t = do
  inc_inters e
  subst_dp0 e k Zer
  subst_dp1 e k Zer
  wnf e s t

-- ! X &L = 1+n
wnf_dpn_suc :: Env -> Stack -> Name -> Lab -> Term -> Term -> IO Term
wnf_dpn_suc e s k l p t = do
  inc_inters e
  n <- fresh e
  regis_dup e n l p
  subst_dp0 e k (Suc (Dp0 n))
  subst_dp1 e k (Suc (Dp1 n))
  wnf e s t

-- ! X &L = Λ{0:z;1+:s}
wnf_dpn_swi :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> IO Term
wnf_dpn_swi e s k l vz vs t = do
  inc_inters e
  z <- fresh e
  sc <- fresh e
  regis_dup e z l vz
  regis_dup e sc l vs
  subst_dp0 e k (Swi (Dp0 z) (Dp0 sc))
  subst_dp1 e k (Swi (Dp1 z) (Dp1 sc))
  wnf e s t

-- ! X &L = Nam(N)
wnf_dpn_nam :: Env -> Stack -> Name -> Lab -> String -> Term -> IO Term
wnf_dpn_nam e s k l n t = do
  inc_inters e
  subst_dp0 e k (Nam n)
  subst_dp1 e k (Nam n)
  wnf e s t

-- ((f ~> g % m) a)
wnf_app_cal :: Env -> Stack -> Term -> Term -> M.Map Name Term -> Term -> IO Term
wnf_app_cal e s f g m a = do
  putStrLn $ ">> wnf_app_cal         : " ++ show (Cal f g m) ++ " " ++ show a
  -- Inspect the structure of the book term g.
  case g of
    Lam fx ff -> wnf_app_cal_lam e s f fx ff m a
    Swi fz fs -> wnf_app_cal_swi e s f fz fs m a
    _         -> wnf_unwind e s (App (Cal f g m) a)

-- ((f ~> λx.g % m) a) -> (f x) ~> g % {m, x→a}
wnf_app_cal_lam :: Env -> Stack -> Term -> Name -> Term -> M.Map Name Term -> Term -> IO Term
wnf_app_cal_lam e s f x g m a = do
  putStrLn $ ">> wnf_app_cal_lam     : " ++ show (Cal f (Lam x g) m) ++ " " ++ show a
  inc_inters e
  -- Add the substitution x->a to the map m (Lazy substitution).
  let m' = M.insert x a m
  -- We use (Var x) here conceptually; the actual substitution is tracked in m'.
  wnf_enter e s (Cal (App f (Var x)) g m')

-- ((f ~> Λ{0:z;1+:s} % m) a)
wnf_app_cal_swi :: Env -> Stack -> Term -> Term -> Term -> M.Map Name Term -> Term -> IO Term
wnf_app_cal_swi e s f z sc m a = do
  -- Evaluate the argument 'a' to determine the interaction.
  !a_wnf <- wnf e [] a
  putStrLn $ ">> wnf_app_cal_swi     : " ++ show (Cal f (Swi z sc) m) ++ " " ++ show a ++ "→" ++ show a_wnf
  case a_wnf of
    Zer       -> wnf_app_cal_swi_zer e s f z m
    Suc n     -> wnf_app_cal_swi_suc e s f sc m n
    Sup l b c -> wnf_app_cal_swi_sup e s f z sc m l b c
    Nam k     -> wnf_unwind e s (App f (Nam k))
    _         -> wnf_unwind e s (App (Cal f (Swi z sc) m) a_wnf)

-- ((f ~> Λ{...} % m) 0) -> (f 0) ~> z % m
wnf_app_cal_swi_zer :: Env -> Stack -> Term -> Term -> M.Map Name Term -> IO Term
wnf_app_cal_swi_zer e s f z m = do
  putStrLn $ ">> wnf_app_cal_swi_zer : " ++ show f ++ "~>Λ{0:" ++ show z ++ ";1+:...} 0"
  inc_inters e
  wnf_enter e s (Cal (App f Zer) z m)

-- ((f ~> Λ{...} % m) 1+n) -> ((λp.(f 1+p) ~> s % m) n)
wnf_app_cal_swi_suc :: Env -> Stack -> Term -> Term -> M.Map Name Term -> Term -> IO Term
wnf_app_cal_swi_suc e s f sc m n = do
  putStrLn $ ">> wnf_app_cal_swi_suc : " ++ show f ++ "~>Λ{0:...;1+:" ++ show sc ++ "} 1+" ++ show n
  inc_inters e
  p <- fresh e
  let cal_term = Cal (Lam p (App f (Suc (Var p)))) sc m
  wnf_enter e s (App cal_term n)

-- ((f ~> Λ{...} % m) &L{a,b})
wnf_app_cal_swi_sup :: Env -> Stack -> Term -> Term -> Term -> M.Map Name Term -> Lab -> Term -> Term -> IO Term
wnf_app_cal_swi_sup e s f z sc m l a b = do
  putStrLn $ ">> wnf_app_cal_swi_sup : " ++ show (Cal f (Swi z sc) m) ++ " &" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  inc_inters e

  -- 1. Duplicate the context f (the caller).
  f' <- fresh e
  regis_dup e f' l f

  -- 2. Duplicate the resources (the substitution map m). THIS IS THE FIX.
  (m0, m1) <- dup_substs e l m

  -- 3. Structurally duplicate the branches z and sc (book terms) for fresh binders.
  (z0, z1) <- alloc_dup e z
  (sc0, sc1) <- alloc_dup e sc

  let swi0 = Swi z0 sc0
  let swi1 = Swi z1 sc1
  let app0 = App (Cal (Dp0 f') swi0 m0) a
  let app1 = App (Cal (Dp1 f') swi1 m1) b
  wnf_enter e s (Sup l app0 app1)

-- ! &L X = f ~> g % m
wnf_dpn_cal :: Env -> Stack -> Name -> Lab -> Term -> Term -> M.Map Name Term -> Term -> IO Term
wnf_dpn_cal e s k l f g m t = do
  putStrLn $ ">> wnf_dpn_cal         : ! &" ++ int_to_name l ++ " " ++ int_to_name k ++ " = " ++ show (Cal f g m)
  inc_inters e

  -- 1. Duplicate f.
  f' <- fresh e
  regis_dup e f' l f

  -- 2. Duplicate the resources m.
  (m0, m1) <- dup_substs e l m

  -- 3. Structurally duplicate g (the book term).
  (g0, g1) <- alloc_dup e g

  subst_dp0 e k (Cal (Dp0 f') g0 m0)
  subst_dp1 e k (Cal (Dp1 f') g1 m1)
  wnf_enter e s t

-- WNF: Utils
-- ----------

-- Duplicates the substitution map by duplicating every term inside it.
dup_substs :: Env -> Lab -> M.Map Name Term -> IO (M.Map Name Term, M.Map Name Term)
dup_substs e l m = do
  let binds = M.toList m
  binds' <- mapM (dup_bind e l) binds
  let (binds0, binds1) = unzip binds'
  return (M.fromList binds0, M.fromList binds1)

dup_bind :: Env -> Lab -> (Name, Term) -> IO ((Name, Term), (Name, Term))
dup_bind e l (k, v) = do
  -- Duplicate the term v.
  v' <- fresh e
  regis_dup e v' l v
  -- Map the name k to the corresponding half of the duplicated term.
  return ((k, Dp0 v'), (k, Dp1 v'))

-- WNF: Allocation Helpers
-- -----------------------

-- Helper to allocate (instantiate) a term with an empty substitution map.
alloc :: Env -> Term -> IO Term
alloc e t = wnf_alloc e M.empty t

-- Helper to create two independent allocated copies of a term.
alloc_dup :: Env -> Term -> IO (Term, Term)
alloc_dup e t = do
  t0 <- alloc e t
  t1 <- alloc e t
  return (t0, t1)

-- WNF: Alloc
-- ----------

-- Clones a term, replacing all bound names with fresh ones, and applying substitutions.
wnf_alloc :: Env -> M.Map Name Term -> Term -> IO Term
wnf_alloc e m t = go m M.empty t
  where
    -- m_var: Maps book names to runtime terms (substitutions from 'm' or alpha-renaming from Lam).
    -- m_dup: Maps book names to runtime names for Dp0/Dp1 (alpha-renaming from Dup).
    go :: M.Map Name Term -> M.Map Name Name -> Term -> IO Term

    -- Apply substitution if the variable is in the map.
    go m_var m_dup (Var k) = case M.lookup k m_var of
      Just v  -> return v
      Nothing -> return (Var k) -- Free variable

    -- Apply alpha-renaming for duplication variables.
    go m_var m_dup (Dp0 k) = case M.lookup k m_dup of
      Just k' -> return (Dp0 k')
      Nothing -> return (Dp0 k)

    go m_var m_dup (Dp1 k) = case M.lookup k m_dup of
      Just k' -> return (Dp1 k')
      Nothing -> return (Dp1 k)

    -- Alpha-rename the binder to avoid capture and ensure freshness.
    go m_var m_dup (Lam k f) = do
      k' <- fresh e
      -- Map the book name k to the fresh runtime variable k'. This shadows any outer substitution for k.
      let m_var' = M.insert k (Var k') m_var
      f' <- go m_var' m_dup f
      return (Lam k' f')

    -- Alpha-rename the duplication variable.
    go m_var m_dup (Dup k l v t) = do
      v' <- go m_var m_dup v
      k' <- fresh e
      -- Map the book name k to the fresh runtime name k' for Dp0/Dp1 lookup.
      let m_dup' = M.insert k k' m_dup
      t' <- go m_var m_dup' t
      return (Dup k' l v' t')

    -- Structural recursion.
    go m_var m_dup (App f x) = do
      f' <- go m_var m_dup f
      x' <- go m_var m_dup x
      return (App f' x')

    go m_var m_dup (Sup l a b) = do
      a' <- go m_var m_dup a
      b' <- go m_var m_dup b
      return (Sup l a' b')

    go m_var m_dup (Suc n) = do
      n' <- go m_var m_dup n
      return (Suc n')

    go m_var m_dup (Swi z s) = do
      z' <- go m_var m_dup z
      s' <- go m_var m_dup s
      return (Swi z' s')

    -- Handle nested Cal terms (if they appear in the input term/book).
    go m_var m_dup (Cal f g m_inner) = do
      f' <- go m_var m_dup f
      g' <- go m_var m_dup g
      -- Apply substitution to the terms inside the nested substitution map.
      m_inner' <- mapM (go m_var m_dup) m_inner
      return (Cal f' g' m_inner')

    go m_var m_dup t = return t -- Era, Zer, Ref, Nam

-- Normalization
-- =============

nf :: Env -> Int -> Term -> IO Term
nf e d x = do { !x0 <- wnf e [] x ; go e d x0 } where
  go :: Env -> Int -> Term -> IO Term
  go e d (Nam k) = do
    return $ Nam k
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
    subst_var e k (Nam (int_to_name d))
    !f0 <- nf e (d + 1) f
    return $ Lam d f0
  go e d (Dup k l v t) = do
    !v0 <- nf e d v
    subst_dp0 e k (Nam (int_to_name d))
    subst_dp1 e k (Nam (int_to_name d))
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
  -- Cal should have been eliminated by wnf.
  go e d (Cal f g m) = do
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

-- TODO: the test function receives:
-- - the source of a Book
-- - the source of a Term
-- And parses the book, the term, then runs
-- Exactly like the 'main' below
run :: String -> String -> IO ()
run book_src term_src = do
  let book = read_book book_src
  let term = read_term term_src
  !env <- new_env book
  !ini <- getCPUTime
  !nf0 <- nf env 1 term
  -- !nf1 <- nf env 1 nf0
  !end <- getCPUTime
  !itr <- readIORef (env_inters env)
  let diff = fromIntegral (end - ini) / (10^12)
  let rate = fromIntegral itr / diff
  putStrLn $ show nf0
  putStrLn $ "- Itrs: " ++ show itr ++ " interactions"
  printf "- Time: %.3f seconds\n" (diff :: Double)
  printf "- Perf: %.2f M interactions/s\n" (rate / 1000000 :: Double)

book :: String
book = """
  @c_true  = λt. λf. t
  @c_false = λt. λf. f
  @c_not   = λb. λt. λf. (b f t)

  @id  = λa.a
  @not = Λ{0:1+0;1+:λp.0}
  @dbl = Λ{0:0;1+:λp.1+1+(@dbl p)}
  @and = Λ{0:Λ{0:0;1+:λp.0};1+:λp.Λ{0:0;1+:λp.1+0}}
  @add = Λ{0:λb.b;1+:λa.λb.1+(@add a b)}
  @sum = Λ{0:0;1+:λp.!P&S=p;1+(@add P₀ (@sum P₁))}


  @foo = λx.Λ{0:x;1+:λp.x}
"""

main :: IO ()
-- main = run book $ "((" ++ f 18 ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"
-- main = run book "λx.(@dbl 1+1+x)" -- λa.1+1+1+1+(^@dbl ^a)
-- main = run book "(@not 0)" -- 1+0
-- main = run book "(@not 1+0)" -- 0
-- main = run book "! F & L = @id; !G & L = F₀; λx.(G₁ x)" -- λa.^a
-- main = run book "(@and 0 0)" -- 0
-- main = run book "(@and &L{0,1+0} 1+0)" -- &L{0,1+0}
-- main = run book "(@and &L{1+0,0} 1+0)" -- &L{1+0,0}
-- main = run book "(@and 1+0 &L{0,1+0})" -- &L{0,1+0}
-- main = run book "(@and 1+0 &L{1+0,0})" -- &L{1+0,0}
-- main = run book "λx.(@and 0 x)" -- λa.((^@and 0) ^a)
-- main = run book "λx.(@and x 0)" -- λa.((^@and ^a) 0)
-- main = run book "(@sum 1+1+1+0)" -- 1+1+1+1+1+1+0
-- main = run book "λx.(@sum 1+1+1+x)"
-- main = run book "(@foo X 1+0)" -- X
main = run book "(@foo v &L{0,1+0})"
