{-# LANGUAGE BangPatterns, CPP #-}

#include "hvm4.hs"

-- Evaluation
-- ==========

data EvalResult = EvalResult
  { eval_env  :: !Env
  , eval_norm :: !Term
  , eval_itrs :: !Int
  , eval_time :: !Double
  , eval_perf :: !Double
  }

eval_term :: Book -> Term -> Bool -> IO EvalResult
eval_term bk term normalize = do
  !env <- new_env bk
  !ini <- getCPUTime
  let lazy_collapse = not normalize
  val <- collapse lazy_collapse env (Alo [] term)
  when normalize $ force_term val
  !val <- if normalize then snf env 1 val else return val
  !end <- getCPUTime
  !itr <- readIORef (env_itrs env)
  !dt  <- return $ fromIntegral (end - ini) / (10 ^ 12)
  !ips <- return $ fromIntegral itr / dt
  return EvalResult
    { eval_env  = env
    , eval_norm = val
    , eval_itrs = itr
    , eval_time = dt
    , eval_perf = ips
    }

-- CLI
-- ===

#ifndef TEST

data CliOpts = CliOpts
  { opt_stats    :: !Bool
  , opt_collapse :: !(Maybe (Maybe Int))
  }

parse_opts :: [String] -> Either String CliOpts
parse_opts = go (CliOpts False Nothing) where
  go opts []        = Right opts
  go opts ("-s":xs) = go (opts { opt_stats = True }) xs
  go opts (('-':'C':n):xs)
    | has_c     = Left "Duplicate -C option"
    | null n    = go (opts { opt_collapse = Just Nothing }) xs
    | valid_n   = go (opts { opt_collapse = Just (Just (read n)) }) xs
    | otherwise = Left $ "Invalid -C value: " ++ n
    where has_c   = opt_collapse opts /= Nothing
          valid_n = all isDigit n
  go _ (x:_) = Left $ "Unknown option: " ++ x

main :: IO ()
main = do
  args <- getArgs

  (file, opts) <- case args of
    []    -> hPutStrLn stderr "Usage: ./main <file.hvm> [-s] [-C[N]]" >> exitFailure
    (f:o) -> return (f, o)

  CliOpts{ opt_stats = stats, opt_collapse = coll } <- case parse_opts opts of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right o  -> return o

  book <- read_book file
  let normalize = coll == Nothing
  EvalResult env val itrs dt ips <- eval_term book (Ref (name_to_int "main")) normalize

  case coll of
    Nothing -> print val
    Just lim -> do
      let terms = flatten val
      forM_ (maybe terms (`take` terms) lim) $ \t -> do
        t' <- snf env 1 t
        print t'

  when stats $ do
    putStrLn $ "- Itrs: " ++ show itrs ++ " interactions"
    printf "- Time: %.3f seconds\n" dt
    printf "- Perf: %.2f M interactions/s\n" (ips / 1e6)

#endif
