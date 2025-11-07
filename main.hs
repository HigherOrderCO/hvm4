{-# LANGUAGE MultilineStrings #-}

import Data.Char (isAlphaNum)
import Data.Function (fix)
import Data.IORef
import Debug.Trace
import System.IO.Unsafe
import Text.ParserCombinators.ReadP
import qualified Data.Map as M

type Lab   = String
type Name  = String
type Map a = M.Map String a

-- dp0 ::= x₀
-- dp1 ::= x₁
-- era ::= &{}
-- sup ::= &L{a,b}
-- dup ::= !x&L=v;t
-- var ::= x
-- lam ::= λx.f
-- app ::= (f x)
-- nam ::= name
-- dry ::= (name arg)
data Term
  = Nam Name
  | Var Name
  | Dp0 Name
  | Dp1 Name
  | Era
  | Sup Lab Term Term
  | Dup Name Lab Term Term
  | Lam Name Term
  | Abs Name Term
  | Dry Term Term
  | App Term Term

instance Show Term where
  show (Nam k)       = k
  show (Dry f x)     = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Var k)       = k
  show (Dp0 k)       = k ++ "₀"
  show (Dp1 k)       = k ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ k ++ "&" ++ l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ k ++ "." ++ show f
  show (Abs k f)     = "λ" ++ k ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"

-- Environment
-- ===========

data Env = Env
  { inters  :: Int
  , var_new :: Int
  , dup_new :: Int
  , var_map :: Map Term
  , dp0_map :: Map Term
  , dp1_map :: Map Term
  , dup_map :: Map (Lab,Term)
  } deriving Show

names :: String -> [String]
names abc = fix $ \x -> [""] ++ concatMap (\s -> Prelude.map (:s) abc) x

env :: Env
env = Env 0 0 0 M.empty M.empty M.empty M.empty

fresh :: (Env -> Int) -> (Env -> Int -> Env) -> String -> Env -> (Env, String)
fresh get set chars s = (set s (get s + 1), "$" ++ (names chars) !! (get s + 1))

fresh_var = fresh var_new (\s n -> s { var_new = n }) ['a'..'z']
fresh_dup = fresh dup_new (\s n -> s { dup_new = n }) ['A'..'Z']

subst :: (Env -> Map a) -> (Env -> Map a -> Env) -> Env -> String -> a -> Env
subst get set s k v = set s (M.insert k v (get s))

subst_var = subst var_map (\s m -> s { var_map = m })
subst_dp0 = subst dp0_map (\s m -> s { dp0_map = m })
subst_dp1 = subst dp1_map (\s m -> s { dp1_map = m })
delay_dup = subst dup_map (\s m -> s { dup_map = m })

taker :: (Env -> Map a) -> (Env -> Map a -> Env) -> Env -> String -> (Maybe a, Env)
taker get set s k = let (mt, m) = M.updateLookupWithKey (\_ _ -> Nothing) k (get s) in (mt, set s m)

take_var = taker var_map (\s m -> s { var_map = m })
take_dp0 = taker dp0_map (\s m -> s { dp0_map = m })
take_dp1 = taker dp1_map (\s m -> s { dp1_map = m })
take_dup = taker dup_map (\s m -> s { dup_map = m })

inc_inters :: Env -> Env
inc_inters s = s { inters = inters s + 1 }

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

name :: ReadP String
name = lexeme parse_nam

parse_term :: ReadP Term
parse_term = lexeme $ choice
  [ parse_lam
  , parse_dup
  , parse_app
  , parse_sup
  , parse_era
  , parse_var
  ]

parse_app :: ReadP Term
parse_app = do
  lexeme (char '(')
  ts <- many1 parse_term
  lexeme (char ')')
  case ts of
    (t:rest) -> return (Prelude.foldl App t rest)
    _        -> pfail

parse_lam :: ReadP Term
parse_lam = do
  lexeme (choice [char 'λ', char '\\'])
  k <- name
  lexeme (char '.')
  body <- parse_term
  return $ Lam k body

parse_dup :: ReadP Term
parse_dup = do
  lexeme (char '!')
  k <- name
  lexeme (char '&')
  l <- name
  lexeme (char '=')
  v <- parse_term
  lexeme (char ';')
  t <- parse_term
  return $ Dup k l v t

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- name
  lexeme (char '{')
  a <- parse_term
  lexeme (char ',')
  b <- parse_term
  lexeme (char '}')
  return $ Sup l a b

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_var :: ReadP Term
parse_var = do
  k <- name
  choice
    [ string "₀"  >> return (Dp0 k)
    , string "₁"  >> return (Dp1 k)
    , return (Var k)
    ]

parse_nam :: ReadP String
parse_nam = munch1 $ \c
  -> c >= 'a' && c <= 'z'
  || c >= 'A' && c <= 'Z'
  || c >= '0' && c <= '9'
  || c == '_' || c == '/'

read_term :: String -> Term
read_term s = case readP_to_S (parse_term <* skipSpaces <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse"

-- Evaluation
-- ==========

wnf :: Env -> Term -> (Env,Term)
wnf s t = go s t where
  go s (App f x)     = let (s0,f0) = wnf s f in app s0 f0 x
  go s (Dup k l v t) = wnf (delay_dup s k (l,v)) t
  go s (Var x)       = var s x
  go s (Dp0 x)       = dp0 s x
  go s (Dp1 x)       = dp1 s x
  go s f             = (s,f)

app :: Env -> Term -> Term -> (Env,Term)
app s (Nam fk)       x = app_nam s fk x
app s (Dry df dx)    x = app_dry s df dx x
app s (Lam fk ff)    x = app_lam s fk ff x
app s (Sup fl fa fb) x = app_sup s fl fa fb x
app s f              x = (s , App f x)

dup :: Env -> String -> Lab -> Term -> Term -> (Env,Term)
dup s k l (Nam vk)       t = dup_nam s k l vk t
dup s k l (Dry vf vx)    t = dup_dry s k l vf vx t
dup s k l (Lam vk vf)    t = dup_lam s k l vk vf t
dup s k l (Sup vl va vb) t = dup_sup s k l vl va vb t
dup s k l v              t = (s , Dup k l v t)

-- Interactions
-- ============

-- (λx.f v)
-- ---------- app-lam
-- x ← v
-- f
app_lam s fx ff v = 
  let s0 = inc_inters s in
  let s1 = subst_var s0 fx v in
  wnf s1 ff

-- (&fL{fa,fb} v)
-- -------------------- app-sup
-- ! x &fL = v
-- &fL{(fa x₀),(fa x₁)}
app_sup s fL fa fb v =
  let s0     = inc_inters s in
  let (s1,x) = fresh_dup s0 in
  let app0   = App fa (Dp0 x) in
  let app1   = App fb (Dp1 x) in
  let sup    = Sup fL app0 app1 in
  let dup    = Dup x fL v sup in
  wnf s1 dup

-- (fk v)
-- ------ app-nam
-- (fk v)
app_nam s fk v = (inc_inters s, Dry (Nam fk) v)

-- ((df dx) v)
-- ----------- app-dry
-- ((df dx) v)
app_dry s df dx v = (inc_inters s, Dry (Dry df dx) v)

-- ! k &L = λvk.vf; t
-- ------------------ dup-lam
-- k₀ ← λx0.g0
-- k₁ ← λx1.g1
-- vk ← &L{x0,x1}
-- ! g &L = vf
-- t
dup_lam s k l vk vf t =
  let s0       = inc_inters s in
  let (s1, x0) = fresh_var s0 in
  let (s2, x1) = fresh_var s1 in
  let (s3, g)  = fresh_dup s2 in
  let s4       = subst_dp0 s3 k  (Lam x0 (Dp0 g)) in
  let s5       = subst_dp1 s4 k  (Lam x1 (Dp1 g)) in
  let s6       = subst_var s5 vk (Sup l (Var x0) (Var x1)) in
  let dup      = Dup g l vf t in
  wnf s6 dup

-- ! k &L = &vL{va,vb}; t
-- ---------------------- dup-sup (==)
-- if l == vL:
--   k₀ ← va
--   k₁ ← vb
--   t
-- else:
--   k₀ ← &vL{a₀,b₀}
--   k₁ ← &vL{a₁,b₁}
--   ! a &L = va
--   ! b &L = vb
--   t
dup_sup s k l vl va vb t
  | l == vl =
    let s0 = inc_inters s in
    let s1 = subst_dp0 s0 k va in
    let s2 = subst_dp1 s1 k vb in
    wnf s2 t
  | l /= vl =
    let s0      = inc_inters s in
    let (s1, a) = fresh_dup s0 in
    let (s2, b) = fresh_dup s1 in
    let s3      = subst_dp0 s2 k (Sup vl (Dp0 a) (Dp0 b)) in
    let s4      = subst_dp1 s3 k (Sup vl (Dp1 a) (Dp1 b)) in
    let dup     = Dup a l va (Dup b l vb t) in
    wnf s4 dup

-- ! k &L = vk; t
-- -------------- dup-nam
-- k₀ ← vk
-- k₁ ← vk
-- t
dup_nam s k l vk t =
  let s0 = inc_inters s in
  let s1 = subst_dp0 s0 k (Nam vk) in
  let s2 = subst_dp1 s1 k (Nam vk) in
  wnf s2 t

-- ! k &L = (vf vx); t
-- --------------------- dup-dry
-- ! f &L = vf
-- ! x &L = vx
-- k₀ ← (f₀ x₀)
-- k₁ ← (f₁ x₁)
-- t
dup_dry s k l vf vx t =
  let s0      = inc_inters s in
  let (s1, f) = fresh_dup s0 in
  let (s2, x) = fresh_dup s1 in
  let s3      = subst_dp0 s2 k (Dry (Dp0 f) (Dp0 x)) in
  let s4      = subst_dp1 s3 k (Dry (Dp1 f) (Dp1 x)) in
  let dup     = Dup f l vf (Dup x l vx t) in
  wnf s4 dup

-- x
-- ------------ var
-- var_map[x]
var :: Env -> String -> (Env,Term)
var s k = case take_var s k of
  (Just t, s0)  -> wnf s0 t
  (Nothing, _)  -> (s, Var k)

-- x₀
-- ---------- dp0
-- dp0_map[x]
dp0 :: Env -> String -> (Env,Term)
dp0 s k = case take_dp0 s k of
  (Just t, s0)  -> wnf s0 t
  (Nothing, _)  -> case take_dup s k of
    (Just (l,v), s0) -> let (s1,v0) = wnf s0 v in dup s1 k l v0 (Dp0 k)
    (Nothing, _)     -> (s, Dp0 k)

-- x₁
-- ---------- dp1
-- dp1_map[x]
dp1 :: Env -> String -> (Env,Term)
dp1 s k = case take_dp1 s k of
  (Just t, s0)  -> wnf s0 t
  (Nothing, _)  -> case take_dup s k of
    (Just (l,v), s0) -> let (s1,v0) = wnf s0 v in dup s1 k l v0 (Dp1 k)
    (Nothing, _)     -> (s, Dp1 k)

-- Normalization
-- =============

nf :: Env -> Term -> (Env,Term)
nf s x = let (s0,x0) = wnf s x in go s0 x0 where
  go s (Nam k)       = (s, Nam k)
  go s (Dry f x)     = let (s0,f0) = nf s f in let (s1,x0) = nf s0 x in (s1, Dry f0 x0)
  go s (Var k)       = (s, Var k)
  go s (Dp0 k)       = (s, Dp0 k)
  go s (Dp1 k)       = (s, Dp1 k)
  go s Era           = (s, Era)
  go s (Sup l a b)   = let (s0,a0) = nf s a in let (s1,b0) = nf s0 b in (s1, Sup l a0 b0)
  go s (Dup k l v t) = let (s0,v0) = nf s v in let (s1,t0) = nf s0 t in (s1, Dup k l v0 t0)
  go s (Lam k f)     = let (s0,f0) = nf (subst_var s k (Nam k)) f in (s0, Lam k f0)
  go s (Abs k f)     = let (s0,f0) = nf s f in (s0, Abs k f0)
  go s (App f x)     = let (s0,f0) = nf s f in let (s1,x0) = nf s0 x in (s1, App f0 x0)

-- Main
-- ====



-- f04 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- λx03.(F03₀ (F03₁ x03))
-- """

-- f08 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- !F04 &A = λx03.(F03₀ (F03₁ x03));
    -- !F05 &A = λx04.(F04₀ (F04₁ x04));
    -- !F06 &A = λx05.(F05₀ (F05₁ x05));
    -- !F07 &A = λx06.(F06₀ (F06₁ x06));
    -- λx07.(F07₀ (F07₁ x07))
-- """

-- f12 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- !F04 &A = λx03.(F03₀ (F03₁ x03));
    -- !F05 &A = λx04.(F04₀ (F04₁ x04));
    -- !F06 &A = λx05.(F05₀ (F05₁ x05));
    -- !F07 &A = λx06.(F06₀ (F06₁ x06));
    -- !F08 &A = λx07.(F07₀ (F07₁ x07));
    -- !F09 &A = λx08.(F08₀ (F08₁ x08));
    -- !F10 &A = λx09.(F09₀ (F09₁ x09));
    -- !F11 &A = λx10.(F10₀ (F10₁ x10));
    -- λx11.(F11₀ (F11₁ x11))
-- """

-- f16 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- !F04 &A = λx03.(F03₀ (F03₁ x03));
    -- !F05 &A = λx04.(F04₀ (F04₁ x04));
    -- !F06 &A = λx05.(F05₀ (F05₁ x05));
    -- !F07 &A = λx06.(F06₀ (F06₁ x06));
    -- !F08 &A = λx07.(F07₀ (F07₁ x07));
    -- !F09 &A = λx08.(F08₀ (F08₁ x08));
    -- !F10 &A = λx09.(F09₀ (F09₁ x09));
    -- !F11 &A = λx10.(F10₀ (F10₁ x10));
    -- !F12 &A = λx11.(F11₀ (F11₁ x11));
    -- !F13 &A = λx12.(F12₀ (F12₁ x12));
    -- !F14 &A = λx13.(F13₀ (F13₁ x13));
    -- !F15 &A = λx14.(F14₀ (F14₁ x14));
    -- λx15.(F15₀ (F15₁ x15))
-- """

-- f20 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- !F04 &A = λx03.(F03₀ (F03₁ x03));
    -- !F05 &A = λx04.(F04₀ (F04₁ x04));
    -- !F06 &A = λx05.(F05₀ (F05₁ x05));
    -- !F07 &A = λx06.(F06₀ (F06₁ x06));
    -- !F08 &A = λx07.(F07₀ (F07₁ x07));
    -- !F09 &A = λx08.(F08₀ (F08₁ x08));
    -- !F10 &A = λx09.(F09₀ (F09₁ x09));
    -- !F11 &A = λx10.(F10₀ (F10₁ x10));
    -- !F12 &A = λx11.(F11₀ (F11₁ x11));
    -- !F13 &A = λx12.(F12₀ (F12₁ x12));
    -- !F14 &A = λx13.(F13₀ (F13₁ x13));
    -- !F15 &A = λx14.(F14₀ (F14₁ x14));
    -- !F16 &A = λx15.(F15₀ (F15₁ x15));
    -- !F17 &A = λx16.(F16₀ (F16₁ x16));
    -- !F18 &A = λx17.(F17₀ (F17₁ x17));
    -- !F19 &A = λx18.(F18₀ (F18₁ x18));
    -- λx19.(F19₀ (F19₁ x19))
-- """

-- f24 = """
-- λf. !F00 &A = f;
    -- !F01 &A = λx00.(F00₀ (F00₁ x00));
    -- !F02 &A = λx01.(F01₀ (F01₁ x01));
    -- !F03 &A = λx02.(F02₀ (F02₁ x02));
    -- !F04 &A = λx03.(F03₀ (F03₁ x03));
    -- !F05 &A = λx04.(F04₀ (F04₁ x04));
    -- !F06 &A = λx05.(F05₀ (F05₁ x05));
    -- !F07 &A = λx06.(F06₀ (F06₁ x06));
    -- !F08 &A = λx07.(F07₀ (F07₁ x07));
    -- !F09 &A = λx08.(F08₀ (F08₁ x08));
    -- !F10 &A = λx09.(F09₀ (F09₁ x09));
    -- !F11 &A = λx10.(F10₀ (F10₁ x10));
    -- !F12 &A = λx11.(F11₀ (F11₁ x11));
    -- !F13 &A = λx12.(F12₀ (F12₁ x12));
    -- !F14 &A = λx13.(F13₀ (F13₁ x13));
    -- !F15 &A = λx14.(F14₀ (F14₁ x14));
    -- !F16 &A = λx15.(F15₀ (F15₁ x15));
    -- !F17 &A = λx16.(F16₀ (F16₁ x16));
    -- !F18 &A = λx17.(F17₀ (F17₁ x17));
    -- !F19 &A = λx18.(F18₀ (F18₁ x18));
    -- !F20 &A = λx19.(F19₀ (F19₁ x19));
    -- !F21 &A = λx20.(F20₀ (F20₁ x20));
    -- !F22 &A = λx21.(F21₀ (F21₁ x21));
    -- !F23 &A = λx22.(F22₀ (F22₁ x22));
    -- λx23.(F23₀ (F23₁ x23))
-- """

-- TODO: implement a generic function 'f :: Int -> String' that returns the equivalent of f_n
f :: Int -> String
f n = "λf. " ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00 &A = f;\n    "
  dup i = "!F" ++ pad i ++ " &A = λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));\n    "
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

term = read_term $ "((" ++ f 4 ++ " λX.((X λT0.λF0.F0) λT1.λF1.T1)) λT2.λF2.T2)"

main :: IO ()
main = do
  let res = nf env term
  print $          snd $ res
  print $ inters $ fst $ res

























