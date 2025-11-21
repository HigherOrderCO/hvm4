{-# LANGUAGE CPP #-}

#define TEST
#include "main.hs"

num :: Int -> String
num 0 = "#Z{}"
num n = "#S{" ++ num (n - 1) ++ "}"

f :: Int -> String
f n = "λf." ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00&A=f;"
  dup i = "!F" ++ pad i ++ "&A=λx" ++ pad (i-1) ++ ".F" ++ pad (i-1) ++ "₀(F" ++ pad (i-1) ++ "₁(x" ++ pad (i-1) ++ "));"
  final = "λx" ++ pad (n-1) ++ ".F" ++ pad (n-1) ++ "₀(F" ++ pad (n-1) ++ "₁(x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

book :: String
book = unlines
  [ "@T   = λt. λf. t"
  , "@F   = λt. λf. f"
  , "@NOT = λb. λt. λf. b(f, t)"
  , "@ADD = λa. λb. λs. λz. !S&B=s; a(S₀, b(S₁, z))"
  , "@MUL = λa. λb. λs. λz. a(b(s), z)"
  , "@EXP = λa. λb. b(a)"
  , "@C1  = λs. λx. s(x)"
  , "@K1  = λs. λx. s(x)"
  , "@C2  = λs. !S0&C=s; λx0.S0₀(S0₁(x0))"
  , "@K2  = λs. !S0&K=s; λx0.S0₀(S0₁(x0))"
  , "@C4  = λs. !S0&C=s; !S1&C=λx0.S0₀(S0₁(x0)); λx1.S1₀(S1₁(x1))"
  , "@K4  = λs. !S0&K=s; !S1&K=λx0.S0₀(S0₁(x0)); !S2&K=λx1.S1₀(S1₁(x1)); λx3.S2₀(S2₁(x3))"
  , "@C8  = λs. !S0&C=s; !S1&C=λx0.S0₀(S0₁(x0)); !S2&C=λx1.S1₀(S1₁(x1)); λx3.S2₀(S2₁(x3))"
  , "@K8  = λs. !S0&K=s; !S1&K=λx0.S0₀(S0₁(x0)); !S2&K=λx1.S1₀(S1₁(x1)); λx3.S2₀(S2₁(x3))"
  , "@ZN  = #Z{}"
  , "@SN  = λn. #S{n}"
  , "@dbl = λ{#Z:#Z{}; λ{#S:λp.#S{#S{@dbl(p)}}; &{}}}"
  , "@add = λ{#Z:λb.b; λ{#S:λa.λb.#S{@add(a, b)}; &{}}}"
  , "@sum = λ{#Z:#Z{}; λ{#S:λp.!P&S=p;#S{@add(P₀, @sum(P₁))}; &{}}}"
  ]

tests :: [(String,String)]
tests =
  [ (num 0, num 0)
  , ("("++f 2++")(λX.X(λT0.λF0.F0, λT1.λF1.T1), λT2.λF2.T2)", "λa.λb.a")
  , ("#S{&L{" ++ num 0 ++ "," ++ num 1 ++ "}}", "&L{" ++ num 1 ++ "," ++ num 2 ++ "}")
  , ("#S{&A{&B{" ++ num 0 ++ "," ++ num 1 ++ "},&C{" ++ num 2 ++ "," ++ num 3 ++ "}}}", "&A{&B{" ++ num 1 ++ "," ++ num 2 ++ "},&C{" ++ num 3 ++ "," ++ num 4 ++ "}}")
  , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  , ("λa.λb.!A&L=a;!B&L=b;&L{λx.x(A₀, B₀),λx.x(A₁,B₁)}", "&L{λa.λb.λc.c(a,b),λa.λb.λc.c(a,b)}")
  , ("λt.t(&A{" ++ num 1 ++ "," ++ num 2 ++ "}, " ++ num 3 ++ ")", "&A{λa.a(" ++ num 1 ++ "," ++ num 3 ++ "),λa.a(" ++ num 2 ++ "," ++ num 3 ++ ")}")
  , ("λt.t(" ++ num 1 ++ ", &B{" ++ num 3 ++ "," ++ num 4 ++ "})", "&B{λa.a(" ++ num 1 ++ "," ++ num 3 ++ "),λa.a(" ++ num 1 ++ "," ++ num 4 ++ ")}")
  , ("λt.t(&A{" ++ num 1 ++ "," ++ num 2 ++ "}, &A{" ++ num 3 ++ "," ++ num 4 ++ "})", "&A{λa.a(" ++ num 1 ++ "," ++ num 3 ++ "),λa.a(" ++ num 2 ++ "," ++ num 4 ++ ")}")
  , ("λt.t(&A{" ++ num 1 ++ "," ++ num 2 ++ "}, &B{" ++ num 3 ++ "," ++ num 4 ++ "})", "&A{&B{λa.a(" ++ num 1 ++ "," ++ num 3 ++ "),λa.a(" ++ num 1 ++ "," ++ num 4 ++ ")},&B{λa.a(" ++ num 2 ++ "," ++ num 3 ++ "),λa.a(" ++ num 2 ++ "," ++ num 4 ++ ")}}")
  , ("@NOT(@T)", "λa.λb.b")
  , ("@NOT(@NOT(@T))", "λa.λb.a")
  , ("@C2(@NOT, @T)", "λa.λb.a")
  , ("@ADD(@C2, @C1)", "λa.λb.a(a(a(b)))")
  , ("@ADD(@C1, λf.λx.f(x), @NOT)", "λa.λb.λc.a(b,c)")
  , ("@ADD(@C1, @C1, @NOT)", "λa.λb.λc.a(b,c)")
  , ("@ADD(@C2, @C2)", "λa.λb.a(a(a(a(b))))")
  , ("@ADD(@C4, @C1)", "λa.λb.a(a(a(a(a(b)))))")
  , ("@ADD(@C1, @C4)", "λa.λb.a(a(a(a(a(b)))))")
  , ("@ADD(@C4, @C4)", "λa.λb.a(a(a(a(a(a(a(a(b))))))))")
  , ("@ADD(@C1, @C4, @NOT, @T)", "λa.λb.b")
  , ("@ADD(@C4, @C1, @NOT, @T)", "λa.λb.b")
  , ("@ADD(@C2, @C4, @NOT, @T)", "λa.λb.a")
  , ("@ADD(@C4, @C2, @NOT, @T)", "λa.λb.a")
  , ("@MUL(@C4, @C2)", "λa.λb.a(a(a(a(a(a(a(a(b))))))))")
  , ("@MUL(@C4, @C4)", "λa.λb.a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(b))))))))))))))))")
  , ("@MUL(@C4, @C2, @NOT, @T)", "λa.λb.a")
  , ("@MUL(@C4, @C4, @NOT, @T)", "λa.λb.a")
  , ("@EXP(@C4, @K2)", "λa.λb.a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(b))))))))))))))))")
  , ("@C8(@K8, @NOT, @T)", "λa.λb.a")
  , ("@dbl(#S{#S{#S{#S{#Z{}}}}})", "#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}")
  , ("@sum(#S{#S{#S{#S{#Z{}}}}})", "#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}")
  ]

runTests :: IO ()
runTests = forM_ tests $ \ (src, exp) -> do
  !env <- new_env $ read_book book
  !det <- collapse env $ read_term src
  !det <- show <$> snf env 1 det
  !itr <- readIORef (env_itrs env)
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " → " ++ det ++ " | #" ++ show itr
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = runTests

