f :: Int -> String
f n = "λf." ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00&A=f;"
  dup i = "!F" ++ pad i ++ "&A=λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));"
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

book :: String
book = unlines
  [ "@T   = λt. λf. t"
  , "@F   = λt. λf. f"
  , "@NOT = λb. λt. λf. (b f t)"
  , "@ADD = λa. λb. λs. λz. !S&B=s; (a S₀ (b S₁ z))"
  , "@MUL = λa. λb. λs. λz. (a (b s) z)"
  , "@EXP = λa. λb. (b a)"
  , "@C1  = λs. λx. (s x)"
  , "@K1  = λs. λx. (s x)"
  , "@C2  = λs. !S0&C=s; λx0.(S0₀ (S0₁ x0))"
  , "@K2  = λs. !S0&K=s; λx0.(S0₀ (S0₁ x0))"
  , "@C4  = λs. !S0&C=s; !S1&C=λx0.(S0₀ (S0₁ x0)); λx1.(S1₀ (S1₁ x1))"
  , "@K4  = λs. !S0&K=s; !S1&K=λx0.(S0₀ (S0₁ x0)); !S2&K=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@C8  = λs. !S0&C=s; !S1&C=λx0.(S0₀ (S0₁ x0)); !S2&C=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@K8  = λs. !S0&K=s; !S1&K=λx0.(S0₀ (S0₁ x0)); !S2&K=λx1.(S1₀ (S1₁ x1)); λx3.(S2₀ (S2₁ x3))"
  , "@id  = ^id ~> λa.a"
  , "@not = ^not ~> λ{0:1+0;1+:λp.0}"
  , "@dbl = ^dbl ~> λ{0:0;1+:λp.1+1+(@dbl p)}"
  , "@and = ^and ~> λ{0:λ{0:0;1+:λp.0};1+:λp.λ{0:0;1+:λp.1+0}}"
  , "@add = ^add ~> λ{0:λb.b;1+:λa.λb.1+(@add a b)}"
  , "@sum = ^sum ~> λ{0:0;1+:λp.!P&S=p;1+(@add P₀ (@sum P₁))}"
  , "@foo = ^foo ~> &L{λx.x,λ{0:0;1+:λp.p}}"
  , "@gen = ^gen ~> !F&A=@gen &A{λx.!X&B=x;&B{X₀,1+X₁},λ{0:&C{0,1};1+:λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  , "@prd = ^prd ~> λ{0:0;1+:λp.p}"
  ]

tests :: [(String,String)]
tests =
  [ ("0", "0")
  , ("(@not 0)", "1")
  , ("(@not 1+0)", "0")
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(and 0 a)")
  , ("λx.(@and x 0)", "λa.(and a 0)")
  , ("(@sum 1+1+1+0)", "6")
  , ("λx.(@sum 1+1+1+x)", "λa.3+(add a 2+(add a 1+(add a (sum a))))")
  , ("(@foo 0)", "&L{0,0}")
  , ("(@foo 1+1+1+0)", "&L{3,2}")
  , ("λx.(@dbl 1+1+x)", "λa.4+(dbl a)")
  , ("("++f 2++" λX.(X λT0.λF0.F0 λT1.λF1.T1) λT2.λF2.T2)", "λa.λb.a")
  , ("1+&L{0,1}", "&L{1,2}")
  , ("1+&A{&B{0,1},&C{2,3}}", "&A{&B{1,2},&C{3,4}}")
  , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  , ("λa.λb.!A&L=a;!B&L=b;&L{λx.(x A₀ B₀),λx.(x A₁ B₁)}", "&L{λa.λb.λc.(c a b),λa.λb.λc.(c a b)}")
  , ("λt.(t &A{1,2} 3)", "&A{λa.(a 1 3),λa.(a 2 3)}")
  , ("λt.(t 1 &B{3,4})", "&B{λa.(a 1 3),λa.(a 1 4)}")
  , ("λt.(t &A{1,2} &A{3,4})", "&A{λa.(a 1 3),λa.(a 2 4)}")
  , ("λt.(t &A{1,2} &B{3,4})", "&A{&B{λa.(a 1 3),λa.(a 1 4)},&B{λa.(a 2 3),λa.(a 2 4)}}")
  , ("@gen", "&A{&B{λa.a,λa.1+a},&C{&D{λ{0:0;1+:λa.(gen a)},&E{λ{0:0;1+:λa.1+(gen a)},λ{0:0;1+:λa.2+(gen a)}}},&D{λ{0:1;1+:λa.(gen a)},&E{λ{0:1;1+:λa.1+(gen a)},λ{0:1;1+:λa.2+(gen a)}}}}}")
  , ("λx.(@gen 2+x)", "&A{&B{λa.2+a,λa.3+a},&D{λa.(gen a),&E{λa.2+(gen a),λa.4+(gen a)}}}")
  , ("(@gen 2)", "&A{&B{2,3},&D{&C{0,1},&E{&C{2,3},&C{4,5}}}}")
  , ("!f&DUP=@prd; (f₀ (f₁ 0))", "0")
  , ("2 == 2", "#T")
  , ("3 == 2", "#F")
  , ("(λa.λb.a) == (λx.λy.x)", "#T")
  , ("(λa.λb.a) == (λx.λy.y)", "#F")
  , ("(λx.2+x) == (λy.2+y)", "#T")
  , ("(λx.3+x) == (λy.2+y)", "#F")
  , ("#F && #F", "#F")
  , ("#F && #T", "#F")
  , ("#T && #F", "#F")
  , ("#T && #T", "#T")
  , ("(λt.(t (λa.2+a) (λb.2+b))) == (λu.(u (λx.2+x) (λy.2+y)))", "#T")
  , ("(λt.(t (λa.2+a) (λb.2+b))) == (λu.(u (λx.2+x) (λy.3+y)))", "#F")
  , ("(@NOT @T)", "λa.λb.b")
  , ("(@NOT (@NOT @T))", "λa.λb.a")
  , ("(@C2 @NOT @T)", "λa.λb.a")
  , ("@C2", "λa.λb.(a (a b))")
  , ("(@ADD @C2 @C1)", "λa.λb.(a (a (a b)))")
  , ("(@ADD @C1 λf.λx.(f x) @NOT)", "λa.λb.λc.(a b c)")
  , ("(@ADD @C1 @C1 @NOT)", "λa.λb.λc.(a b c)")
  , ("(@ADD @C2 @C2)", "λa.λb.(a (a (a (a b))))")
  , ("(@ADD @C4 @C1)", "λa.λb.(a (a (a (a (a b)))))")
  , ("(@ADD @C1 @C4)", "λa.λb.(a (a (a (a (a b)))))")
  , ("(@ADD @C4 @C4)", "λa.λb.(a (a (a (a (a (a (a (a b))))))))")
  , ("(@ADD @C1 @C4 @NOT @T)", "λa.λb.b")
  , ("(@ADD @C4 @C1 @NOT @T)", "λa.λb.b")
  , ("(@ADD @C2 @C4 @NOT @T)", "λa.λb.a")
  , ("(@ADD @C4 @C2 @NOT @T)", "λa.λb.a")
  , ("(@MUL @C4 @C2)", "λa.λb.(a (a (a (a (a (a (a (a b))))))))")
  , ("(@MUL @C4 @C4)", "λa.λb.(a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))))")
  , ("(@MUL @C4 @C2 @NOT @T)", "λa.λb.a")
  , ("(@MUL @C4 @C4 @NOT @T)", "λa.λb.a")
  , ("(@EXP @C4 @K2)", "λa.λb.(a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a b))))))))))))))))")
  , ("(@C8 @K8 @NOT @T)", "λa.λb.a")
  ]

test :: IO ()
test = forM_ tests $ \ (src, exp) -> do
  !env <- new_env $ read_book book
  !det <- collapse env $ read_term src
  !det <- show <$> snf env 1 det
  !itr <- readIORef (env_inters env)
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " → " ++ det ++ " | #" ++ show itr
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det
