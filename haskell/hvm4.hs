{-# LANGUAGE BangPatterns, CPP #-}

import Control.Monad (foldM, forM_, when)
import Data.Bits (shiftL)
import Data.Char (isSpace, isDigit)
import Data.IORef
import Data.List (foldl', elemIndex, intercalate)
import System.CPUTime
import System.Directory (canonicalizePath)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>), takeDirectory)
import System.IO (hPutStrLn, stderr)
import Text.Printf
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Config
-- ======

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
  | Lam !Name !Term
  | App !Term !Term
  | Ctr !Name ![Term]
  | Mat !Name !Term !Term
  | Alo ![Name] !Term
  deriving (Eq)

data Book = Book (M.Map Name Term)

data Declaration
  = Include FilePath
  | Define Name Term

data Env = Env
  { env_book  :: !Book
  , env_itrs  :: !(IORef Int)
  , env_fresh :: !(IORef Int)
  , env_subst :: !(IORef (IM.IntMap Term))
  , env_dups  :: !(IORef (IM.IntMap (Lab, Term)))
  }

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name k
  show (Cop s k)     = int_to_name k ++ (if s == 0 then "₀" else "₁")
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = k
  show (Dry f x)     = show_app f x
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f x
  show (Ctr k xs)    = "#" ++ int_to_name k ++ "{" ++ intercalate "," (map show xs) ++ "}"
  show (Mat k h m)   = "λ{#" ++ int_to_name k ++ ":" ++ show h ++ ";" ++ show m ++ "}"
  show (Alo s t)     = "@{" ++ intercalate "," (map int_to_name s) ++ "}" ++ show t

show_app :: Term -> Term -> String
show_app f x = case f of
  App _ _ -> init (show f) ++ "," ++ show x ++ ")"
  Dry _ _ -> init (show f) ++ "," ++ show x ++ ")"
  Lam _ _ -> "(" ++ show f ++ ")(" ++ show x ++ ")"
  _       -> show f ++ "(" ++ show x ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

show_dups  :: IM.IntMap (Lab, Term) -> String
show_dups  m = unlines [ "! " ++ int_to_name k ++ " &" ++ int_to_name l ++ " = " ++ show v | (k, (l, v)) <- IM.toList m ]

show_subst :: IM.IntMap Term -> String
show_subst m = unlines [ int_to_name (k `div` 4) ++ suffix (k `mod` 4) ++ " ← " ++ show v | (k, v) <- IM.toList m ]
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
int_to_name n | n <  64 = [alphabet !! n]
              | n >= 64 = int_to_name (n `div` 64) ++ [alphabet !! (n `mod` 64)]

-- Parsing
-- =======

data PState = PState
  { ps_file :: FilePath
  , ps_src  :: String
  , ps_code :: String
  , ps_line :: Int
  , ps_col  :: Int
  , ps_defs :: M.Map Name Term
  , ps_seen :: S.Set FilePath
  }

get_source_line :: String -> Int -> String
get_source_line src line
  | line > 0 && line <= length lns = lns !! (line - 1)
  | otherwise                      = ""
  where lns = lines (src ++ "\n")

parse_error :: IORef PState -> String -> IO a
parse_error ps expected = do
  s <- readIORef ps
  let file = ps_file s
  let line = ps_line s
  let col  = ps_col s
  let src  = ps_src s
  let code = ps_code s
  let curr = case code of { [] -> "EOF" ; c:_ -> show [c] }
  let line_str = get_source_line src line
  hPutStrLn stderr $ "\ESC[1;31mPARSE_ERROR\ESC[0m (" ++ file ++ ":" ++ show line ++ ":" ++ show col ++ ")"
  hPutStrLn stderr $ "- detected: " ++ curr
  hPutStrLn stderr $ "- expected: " ++ expected
  hPutStrLn stderr $ show line ++ " | " ++ line_str
  hPutStrLn stderr $ replicate (length (show line) + 3 + col - 1) ' ' ++ "\ESC[1;31m^\ESC[0m"
  exitFailure

peek :: IORef PState -> IO Char
peek ps = do
  s <- readIORef ps
  return $ case ps_code s of { [] -> '\0' ; c:_ -> c }

step :: IORef PState -> IO ()
step ps = modifyIORef' ps $ \s -> case ps_code s of
  '\n':cs -> s { ps_code = cs, ps_line = ps_line s + 1, ps_col = 1 }
  _   :cs -> s { ps_code = cs, ps_col  = ps_col  s + 1 }
  []      -> s

drop_line ps = do
  c <- peek ps
  step ps
  if c /= '\n' && c /= '\0' then
    drop_line ps
  else
    skip ps

skip :: IORef PState -> IO ()
skip ps = do
  s <- readIORef ps
  case ps_code s of
    '/':'/':_       -> drop_line ps
    c:_ | isSpace c -> step ps >> skip ps
    _               -> return ()

consume :: String -> IORef PState -> IO ()
consume str ps = do
  forM_ str $ \c -> do
    c' <- peek ps
    if c == c' 
      then step ps 
      else parse_error ps ("'" ++ [c] ++ "'")
  skip ps

parse_name :: IORef PState -> IO Name
parse_name ps = do
  c <- peek ps
  if c `elem` alphabet_first 
    then do
      step ps
      rest <- collect_name_chars
      let nam = c : rest
      skip ps
      return (name_to_int nam)
    else parse_error ps "name"
  where
    collect_name_chars = do
      c <- peek ps
      if c `elem` alphabet 
        then do
          step ps
          rest <- collect_name_chars
          return (c : rest)
        else return []

parse_str_until :: Char -> IORef PState -> IO String
parse_str_until end ps = do
  c <- peek ps
  if c == end 
    then return [] 
    else do
      step ps
      rest <- parse_str_until end ps
      return (c : rest)

parse_term :: IORef PState -> IO Term
parse_term ps = do
  c <- peek ps
  t <- case c of
    'λ' -> parse_lam ps
    '!' -> parse_dup ps
    '&' -> parse_sup ps
    '#' -> parse_ctr ps
    '@' -> parse_ref ps
    '(' -> parse_par ps
    _   -> parse_var ps
  parse_app t ps

parse_lam :: IORef PState -> IO Term
parse_lam ps = do
  consume "λ" ps
  c <- peek ps
  if c == '{' 
    then parse_mat ps 
    else do
      nam <- parse_name ps
      consume "." ps
      bod <- parse_term ps
      return $ Lam nam bod

parse_mat :: IORef PState -> IO Term
parse_mat ps = do
  consume "{" ps
  parse_mat_body
  where
    parse_mat_body = do
      c <- peek ps
      case c of
        '}' -> do
          consume "}" ps 
          return Era
        '#' -> do
          consume "#" ps
          nam <- parse_name ps
          consume ":" ps
          val <- parse_term ps
          c2 <- peek ps
          when (c2 == ';') (consume ";" ps)
          nxt <- parse_mat_body
          return $ Mat nam val nxt
        _ -> do
          t <- parse_term ps
          consume "}" ps
          return t

parse_dup :: IORef PState -> IO Term
parse_dup ps = do
  consume "!" ps
  nam <- parse_name ps
  consume "&" ps
  lab <- parse_name ps
  consume "=" ps
  val <- parse_term ps
  consume ";" ps
  bod <- parse_term ps
  return $ Dup nam lab val bod

parse_sup :: IORef PState -> IO Term
parse_sup ps = do
  consume "&" ps
  c <- peek ps
  if c == '{' 
    then do
      consume "{" ps
      consume "}" ps
      return Era
    else do
      lab <- parse_name ps
      consume "{" ps
      t1 <- parse_term ps
      consume "," ps
      t2 <- parse_term ps
      consume "}" ps
      return $ Sup lab t1 t2

parse_ctr :: IORef PState -> IO Term
parse_ctr ps = do
  consume "#" ps
  nam <- parse_name ps
  consume "{" ps
  args <- parse_comma_separated_terms
  return $ Ctr nam args
  where
    parse_comma_separated_terms = do
      c <- peek ps
      if c == '}' 
        then do
          consume "}" ps 
          return []
        else do
          t <- parse_term ps
          c2 <- peek ps
          if c2 == ',' 
            then do
              consume "," ps
              rest <- parse_comma_separated_terms
              return (t : rest)
            else do
              consume "}" ps 
              return [t]

parse_ref :: IORef PState -> IO Term
parse_ref ps = do
  consume "@" ps
  c <- peek ps
  if c == '{' 
    then parse_alo ps
    else do
      nam <- parse_name ps
      return $ Ref nam
  where
    parse_alo ps = do
      consume "{" ps
      ns <- parse_comma_separated_names
      t <- parse_term ps
      return $ Alo ns t
    
    parse_comma_separated_names = do
      n <- parse_name ps
      c2 <- peek ps
      if c2 == ',' 
        then do
          consume "," ps
          rest <- parse_comma_separated_names
          return (n : rest)
        else do
          consume "}" ps 
          return [n]

parse_par :: IORef PState -> IO Term
parse_par ps = do
  consume "(" ps
  t <- parse_term ps
  consume ")" ps
  return t

parse_var :: IORef PState -> IO Term
parse_var ps = do
  nam <- parse_name ps
  c <- peek ps
  case c of
    '₀' -> do
      consume "₀" ps 
      return (Cop 0 nam)
    '₁' -> do
      consume "₁" ps 
      return (Cop 1 nam)
    _   -> return (Var nam)

parse_app :: Term -> IORef PState -> IO Term
parse_app f ps = do
  c <- peek ps
  if c == '(' 
    then do
      consume "(" ps
      args <- parse_comma_separated_args
      parse_app (foldl' App f args) ps
    else return f
  where
    parse_comma_separated_args = do
      c <- peek ps
      if c == ')' 
        then do
          consume ")" ps 
          return []
        else do
          t <- parse_term ps
          c2 <- peek ps
          if c2 == ',' 
            then do
              consume "," ps
              rest <- parse_comma_separated_args
              return (t : rest)
            else do
              consume ")" ps 
              return [t]

read_book :: FilePath -> IO Book
read_book path = do
  path <- canonicalizePath path
  let initial_state = PState path "" "" 1 1 M.empty S.empty
  ps <- newIORef initial_state
  do_include ps path
  s <- readIORef ps
  return $ Book (M.map bruijn (ps_defs s))

do_include :: IORef PState -> FilePath -> IO ()
do_include ps path = do
  s <- readIORef ps
  if S.member path (ps_seen s) 
    then return () 
    else do
      code <- readFile path
      let new_state = s { ps_file = path
                        , ps_src = code
                        , ps_code = code
                        , ps_line = 1
                        , ps_col = 1
                        , ps_seen = S.insert path (ps_seen s) 
                        }
      writeIORef ps new_state
      skip ps
      parse_defs ps
      restore_old_state
  where
    restore_old_state = do
      s' <- readIORef ps
      s  <- readIORef ps
      let restored = s' { ps_file = ps_file s
                        , ps_src = ps_src s
                        , ps_code = ps_code s
                        , ps_line = ps_line s
                        , ps_col = ps_col s 
                        }
      writeIORef ps restored

parse_defs :: IORef PState -> IO ()
parse_defs ps = do
  c <- peek ps
  case c of
    '\0' -> return ()
    '#'  -> do
      parse_include ps
      parse_defs ps
    '@'  -> do
      parse_definition ps
      parse_defs ps
    _    -> parse_error ps "definition or #include"
  where
    parse_include ps = do
      consume "#include" ps
      consume "\"" ps
      f <- parse_str_until '"' ps
      consume "\"" ps
      s <- readIORef ps
      let dir = takeDirectory (ps_file s)
      p <- canonicalizePath (dir </> f)
      do_include ps p
    
    parse_definition ps = do
      consume "@" ps
      nam <- parse_name ps
      consume "=" ps
      val <- parse_term ps
      update_definitions nam val
      where
        update_definitions nam val = 
          modifyIORef' ps $ \s -> 
            s { ps_defs = M.insert nam val (ps_defs s) }

read_term :: String -> Term
read_term _ = error "read_term not supported in IO parser without IO"

-- Environment
-- ===========

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 1
  sub <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids sub dm

inc_itrs :: Env -> IO ()
inc_itrs e = do
  !n <- readIORef (env_itrs e)
  writeIORef (env_itrs e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (env_fresh e)
  writeIORef (env_fresh e) (n + 1)
  return ((n `shiftL` 6) + 63)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = atomicModifyIORef' (env_dups  e) $ \m -> (IM.delete k m, IM.lookup k m)

take_sub :: Env -> Name -> IO (Maybe Term)
take_sub e k = atomicModifyIORef' (env_subst e) $ \m -> (IM.delete k m, IM.lookup k m)

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dups  e) (IM.insert k (l, v))

subst :: Env -> Name -> Term -> IO ()
subst e k v = modifyIORef' (env_subst e) (IM.insert k v)

-- Quoting
-- =======

bruijn :: Term -> Term
bruijn t = go IM.empty 0 t where
  go :: IM.IntMap Int -> Int -> Term -> Term
  go env d t = case t of
    Var k       -> Var   (d - 1 - env IM.! k)
    Cop s k     -> Cop s (d - 1 - env IM.! k)
    Ref k       -> Ref k
    Nam k       -> Nam k
    Dry f x     -> Dry (go env d f) (go env d x)
    Era         -> Era
    Sup l a b   -> Sup l (go env d a) (go env d b)
    Dup k l v b -> Dup k l (go env d v) (go (IM.insert k d env) (d + 1) b)
    Lam k f     -> Lam k (go (IM.insert k d env) (d + 1) f)
    App f x     -> App (go env d f) (go env d x)
    Ctr k xs    -> Ctr k (map (go env d) xs)
    Mat k h m   -> Mat k (go env d h) (go env d m)
    Alo s b     -> Alo s (go env d b)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Cop 0 k , Cop 1 k)

clone_list :: Env -> Lab -> [Term] -> IO ([Term], [Term])
clone_list e l []     = return ([], [])
clone_list e l (h:t) = do
  (h0, h1) <- clone e l h
  (t0, t1) <- clone_list e l t
  return (h0:t0, h1:t1)

-- WNF: Weak Normal Form
-- =====================

type WnfApp = Env -> Term -> Term -> IO Term
type WnfDup = Int -> Env -> Name -> Lab -> Term -> IO Term

wnf :: Env -> Term -> IO Term
wnf e term = do
  when debug $ putStrLn $ "wnf: " ++ show term
  case term of
    Var k -> do
      var e k
    Cop s k -> do
      got <- take_dup e k
      case got of
        Just (l, v) -> do
          v <- wnf e v
          case v of
            Era   -> dup_era s e k l v
            Sup{} -> dup_sup s e k l v
            Lam{} -> dup_lam s e k l v
            Nam{} -> dup_nam s e k l v
            Dry{} -> dup_dry s e k l v
            Ctr{} -> dup_ctr s e k l v
            Mat{} -> dup_mat s e k l v
            _     -> return (Dup k l v (Cop s k))
        Nothing -> do
          cop s e k
    App f x -> do
      f <- wnf e f
      case f of
        Era   -> app_era e f x
        Sup{} -> app_sup e f x
        Lam{} -> app_lam e f x
        Nam{} -> app_nam e f x
        Dry{} -> app_dry e f x
        Mat k h m -> do
          x <- wnf e x
          case x of
            Era      -> app_mat_era e f x
            Sup{}    -> app_mat_sup e f x
            Ctr k' a -> app_mat_ctr e f k h m k' a
            _        -> return (App f x)
        _ -> return (App f x)
    Dup k l v t -> do
      make_dup e k l v
      wnf e t
    Ref k -> do
      ref e k
    Alo s t -> case t of
      Var k       -> wnf e $ Var (s !! k)
      Cop c k     -> wnf e $ Cop c (s !! k)
      Ref k       -> wnf e $ Ref k
      Nam k       -> wnf e $ Nam k
      Dry f x     -> wnf e $ Dry (Alo s f) (Alo s x)
      Era         -> wnf e $ Era
      Sup l a b   -> wnf e $ Sup l (Alo s a) (Alo s b)
      Dup k l v t -> do { x <- fresh e ; wnf e $ Dup x l (Alo s v) (Alo (x:s) t) }
      Lam k f     -> do { x <- fresh e ; wnf e $ Lam x (Alo (x:s) f) }
      App f x     -> wnf e $ App (Alo s f) (Alo s x)
      Ctr k xs    -> wnf e $ Ctr k (map (Alo s) xs)
      Mat k h m   -> wnf e $ Mat k (Alo s h) (Alo s m)
      Alo s' t'   -> error "Nested Alo"
    t -> do
      return t

-- WNF: Interactions
-- =================

var :: Env -> Name -> IO Term
var e k = do
  when debug $ putStrLn $ "var: " ++ show (Var k)
  mt <- take_sub e k
  case mt of
    Just t  -> wnf e t
    Nothing -> return $ Var k

cop :: Int -> Env -> Name -> IO Term
cop i e k = do
  when debug $ putStrLn $ "cop: " ++ show (Cop i k)
  mt <- take_sub e k
  case mt of
    Just t  -> wnf e t
    Nothing -> return $ Cop i k

dup_era :: WnfDup
dup_era i e k _ Era = do
  inc_itrs e
  subst e k Era
  wnf e Era

dup_sup :: WnfDup
dup_sup i e k l (Sup vl va vb)
  | l == vl = do
      inc_itrs e
      if i == 0 then do
        subst e k vb
        wnf e va
      else do
        subst e k va
        wnf e vb
  | otherwise = do
      inc_itrs e
      (va0, va1) <- clone e l va
      (vb0, vb1) <- clone e l vb
      if i == 0 then do
        subst e k (Sup vl va1 vb1)
        wnf e (Sup vl va0 vb0)
      else do
        subst e k (Sup vl va0 vb0)
        wnf e (Sup vl va1 vb1)

dup_lam :: WnfDup
dup_lam i e k l (Lam vk vf) = do
  inc_itrs e
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

dup_nam :: WnfDup
dup_nam i e k _ (Nam n) = do
  inc_itrs e
  subst e k (Nam n)
  wnf e (Nam n)

dup_dry :: WnfDup
dup_dry i e k l (Dry vf vx) = do
  inc_itrs e
  (vf0, vf1) <- clone e l vf
  (vx0, vx1) <- clone e l vx
  if i == 0 then do
    subst e k (Dry vf1 vx1)
    wnf e (Dry vf0 vx0)
  else do
    subst e k (Dry vf0 vx0)
    wnf e (Dry vf1 vx1)

dup_ctr :: WnfDup
dup_ctr i e k l (Ctr kn xs) = do
  inc_itrs e
  (xsA, xsB) <- clone_list e l xs
  if i == 0 then do
    subst e k (Ctr kn xsB)
    wnf e (Ctr kn xsA)
  else do
    subst e k (Ctr kn xsA)
    wnf e (Ctr kn xsB)

dup_mat :: WnfDup
dup_mat i e k l (Mat kn h m) = do
  inc_itrs e
  (hA, hB) <- clone e l h
  (mA, mB) <- clone e l m
  if i == 0 then do
    subst e k (Mat kn hB mB)
    wnf e (Mat kn hA mA)
  else do
    subst e k (Mat kn hA mA)
    wnf e (Mat kn hB mB)

app_era :: WnfApp
app_era e Era v = do
  inc_itrs e
  wnf e Era

app_nam :: WnfApp
app_nam e (Nam fk) v = wnf e (Dry (Nam fk) v)

app_dry :: WnfApp
app_dry e (Dry ff fx) v = wnf e (Dry (Dry ff fx) v)

app_lam :: WnfApp
app_lam e (Lam fx ff) v = do
  inc_itrs e
  subst e fx v
  wnf e ff

app_sup :: WnfApp
app_sup e (Sup fL fa fb) v = do
  inc_itrs e
  (x0,x1) <- clone e fL v
  wnf e (Sup fL (App fa x0) (App fb x1))

app_mat_era :: WnfApp
app_mat_era e f x = do
  inc_itrs e
  wnf e Era

app_mat_sup :: WnfApp
app_mat_sup e (Mat k h m) (Sup l x y) = do
  inc_itrs e
  (h0, h1) <- clone e l h
  (m0, m1) <- clone e l m
  wnf e (Sup l (App (Mat k h0 m0) x) (App (Mat k h1 m1) y))

app_mat_ctr :: Env -> Term -> Int -> Term -> Term -> Int -> [Term] -> IO Term
app_mat_ctr e f k h m k' xs = do
  inc_itrs e
  if k == k' then do
    wnf e (foldl' App h xs)
  else do
    wnf e (App m (Ctr k' xs))

ref :: Env -> Name -> IO Term
ref e k = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_itrs e
      wnf e (Alo [] f)
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

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

    Lam k f -> do
      subst e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'

    App f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ App f' x'

    Ref k -> do
      return $ Ref k

    Nam k -> do
      return $ Nam k

    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'

    Ctr k xs -> do
      xs' <- mapM (snf e d) xs
      return $ Ctr k xs'

    Mat k h m -> do
      h' <- snf e d h
      m' <- snf e d m
      return $ Mat k h' m'

    Alo s t -> do
      error "Should be gone"

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

    (Lam k f) -> do
      fV <- fresh e
      f' <- collapse e f
      inject e (Lam fV (Lam k (Var fV))) [f']

    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f', x']

    Nam n -> do
      return $ Nam n

    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inject e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f', x']

    Ctr k xs -> do
      vs <- mapM (\_ -> fresh e) xs
      as <- mapM (collapse e) xs
      inject e (foldr Lam (Ctr k (map Var vs)) vs) as

    Mat k h m -> do
      hV <- fresh e
      mV <- fresh e
      h' <- collapse e h
      m' <- collapse e m
      inject e (Lam hV (Lam mV (Mat k (Var hV) (Var mV)))) [h', m']

    x -> do
      return $ x

inject :: Env -> Term -> [Term] -> IO Term
inject e f [] = return f
inject e f (h:t) = do
  !h <- wnf e h
  case h of
    Sup l a b -> do
      (f0,f1) <- clone e l f
      (t0,t1) <- clone_list e l t
      a' <- inject e f0 (a:t0)
      b' <- inject e f1 (b:t1)
      return $ Sup l a' b'
    _ -> do
      inject e (App f h) t

flatten :: Term -> [Term]
flatten term = bfs [term] [] where
  bfs []     acc = reverse acc
  bfs (t:ts) acc = case t of
    Sup _ a b -> bfs (ts ++ [a, b]) acc
    _         -> bfs ts (t : acc)
