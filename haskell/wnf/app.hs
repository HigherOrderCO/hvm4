wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s f a = do
  when debug $ putStrLn $ "wnf_app: " ++ show (App f a)
  case f of
    Era       -> wnf_app_era e s f a
    Sup {}    -> wnf_app_sup e s f a
    Lam {}    -> wnf_app_lam e s f a
    Nam {}    -> wnf_app_nam e s f a
    Dry {}    -> wnf_app_dry e s f a
    Swi {}    -> wnf_enter e (FAppF f : s) a
    Get {}    -> wnf_enter e (FAppF f : s) a
    Efq       -> wnf_enter e (FAppF f : s) a
    Use {}    -> wnf_enter e (FAppF f : s) a
    If {}     -> wnf_enter e (FAppF f : s) a
    Mat {}    -> wnf_enter e (FAppF f : s) a
    Gua f0 g0 -> wnf_enter e (FAppG (Tup f0 a) : s) g0
    _         -> wnf_unwind e s (App f a)

wnf_app_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_era e s Era v = do
  inc_inters e
  wnf e s Era

wnf_app_nam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_nam e s (Nam fk) v = wnf e s (Dry (Nam fk) v)

wnf_app_dry :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_dry e s (Dry ff fx) v = wnf e s (Dry (Dry ff fx) v)

wnf_app_lam :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_lam e s (Lam fx ff) v = do
  inc_inters e
  subst VAR e fx v
  wnf e s ff

wnf_app_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_sup e s (Sup fL fa fb) v = do
  inc_inters e
  (x0,x1) <- clone e fL v
  wnf e s (Sup fL (App fa x0) (App fb x1))

wnf_app_f :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_f e s f a = case f of
  Swi {} -> wnf_app_swi e s f a
  Get {} -> wnf_app_get e s f a
  Efq    -> wnf_app_efq e s f a
  Use {} -> wnf_app_use e s f a
  If {}  -> wnf_app_if  e s f a
  Mat {} -> wnf_app_mat e s f a
  _      -> wnf_unwind e s (App f a)

wnf_app_swi :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi e s f@(Swi z sc) a = case a of
  Era    -> wnf_app_swi_era e s f a
  Sup {} -> wnf_app_swi_sup e s f a
  Zer    -> wnf_app_swi_zer e s f a
  Suc {} -> wnf_app_swi_suc e s f a
  _      -> wnf_unwind e s (App f a)

wnf_app_swi_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_era e s (Swi z sc) Era = do
  inc_inters e
  wnf e s Era

wnf_app_swi_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_sup e s (Swi z sc) (Sup l a b) = do
  inc_inters e
  (z0, z1) <- clone e l z
  (s0, s1) <- clone e l sc
  let app0 = App (Swi z0 s0) a
  let app1 = App (Swi z1 s1) b
  wnf_enter e s (Sup l app0 app1)

wnf_app_swi_zer :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_zer e s (Swi z sc) Zer = do
  inc_inters e
  wnf e s z

wnf_app_swi_suc :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_swi_suc e s (Swi z sc) (Suc n) = do
  inc_inters e
  wnf_enter e s (App sc n)

wnf_app_get :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_get e s f@(Get c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Get c0) x) (App (Get c1) y))
  Tup x y -> do
    inc_inters e
    wnf_enter e s (App (App c x) y)
  _ -> wnf_unwind e s (App f a)

wnf_app_efq :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_efq e s Efq a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    wnf_enter e s (Sup l (App Efq x) (App Efq y))
  _ -> wnf_unwind e s (App Efq a)

wnf_app_use :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_use e s f@(Use u) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (u0, u1) <- clone e l u
    wnf_enter e s (Sup l (App (Use u0) x) (App (Use u1) y))
  One -> do
    inc_inters e
    wnf e s u
  _ -> wnf_unwind e s (App f a)

wnf_app_if :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_if e s f@(If ft ff) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (ft0, ft1) <- clone e l ft
    (ff0, ff1) <- clone e l ff
    wnf_enter e s (Sup l (App (If ft0 ff0) x) (App (If ft1 ff1) y))
  Fal -> do
    inc_inters e
    wnf e s ft
  Tru -> do
    inc_inters e
    wnf e s ff
  _ -> wnf_unwind e s (App f a)

wnf_app_mat :: Env -> Stack -> Term -> Term -> IO Term
wnf_app_mat e s f@(Mat n c) a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    (n0, n1) <- clone e l n
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Mat n0 c0) x) (App (Mat n1 c1) y))
  Nil -> do
    inc_inters e
    wnf e s n
  Con h t -> do
    inc_inters e
    wnf_enter e s (App (App c h) t)
  _ -> wnf_unwind e s (App f a)

wnf_app_gua :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua e s f g a = do
  case g of
    Era    -> wnf_app_gua_era e s f g a
    Sup {} -> wnf_app_gua_sup e s f g a
    Lam {} -> wnf_app_gua_lam e s f g a
    Swi {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Get {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Efq    -> wnf_enter e (FAppGF (Tup f g) : s) a
    Use {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    If {}  -> wnf_enter e (FAppGF (Tup f g) : s) a
    Mat {} -> wnf_enter e (FAppGF (Tup f g) : s) a
    Gua {} -> wnf_app_gua_gua e s f g a
    _      -> wnf_unwind e s (App (Tup f g) a)

wnf_app_gua_era :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_era e s f Era a = do
  inc_inters e
  wnf e s Era

wnf_app_gua_sup :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_sup e s f (Sup l x y) a = do
  inc_inters e
  (f0,f1) <- clone e l f
  (a0,a1) <- clone e l a
  let app0 = (App (Gua f0 x) a0)
  let app1 = (App (Gua f1 y) a1)
  wnf_enter e s (Sup l app0 app1)

wnf_app_gua_lam :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_lam e s f (Lam x g) a = do
  inc_inters e
  subst VAR e x a
  wnf_enter e s (Gua (App f (Var x)) g)

wnf_app_gua_gua :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_gua e s f g a = do
  inc_inters e
  wnf_enter e s (Gua (App f a) (App g a))

wnf_app_gua_f :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_f e s f m a = case m of
  Swi {} -> wnf_app_gua_swi e s f m a
  Get {} -> wnf_app_gua_get e s f m a
  Efq    -> wnf_app_gua_efq e s f m a
  Use {} -> wnf_app_gua_use e s f m a
  If {}  -> wnf_app_gua_if  e s f m a
  Mat {} -> wnf_app_gua_mat e s f m a
  _      -> wnf_unwind e s (App (Gua f m) a)

wnf_app_gua_swi :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_swi e s f (Swi z sc) a = case a of
  Era    -> wnf_app_gua_swi_era e s f z sc a
  Sup {} -> wnf_app_gua_swi_sup e s f z sc a
  Zer    -> wnf_app_gua_swi_zer e s f z sc a
  Suc {} -> wnf_app_gua_swi_suc e s f z sc a
  Gua {} -> wnf_app_gua_gua e s f (Swi z sc) a
  _      -> wnf_unwind e s (App f a)

wnf_app_gua_swi_era :: WnfGuaSwi
wnf_app_gua_swi_era e s f z sc Era = do
  wnf_enter e s Era

wnf_app_gua_swi_sup :: WnfGuaSwi
wnf_app_gua_swi_sup e s f z sc (Sup l a b) = do
  inc_inters e
  (f0,f1) <- clone e l f
  (z0,z1) <- clone e l z
  (s0,s1) <- clone e l sc
  let app0 = App (Gua f0 (Swi z0 s0)) a
  let app1 = App (Gua f1 (Swi z1 s1)) b
  wnf_enter e s (Sup l app0 app1)

wnf_app_gua_swi_zer :: WnfGuaSwi
wnf_app_gua_swi_zer e s f z sc Zer = do
  inc_inters e
  wnf_enter e s (Gua (App f Zer) z)

wnf_app_gua_swi_suc :: WnfGuaSwi
wnf_app_gua_swi_suc e s f z sc (Suc n) = do
  inc_inters e
  p <- fresh e
  let fn = (Lam p (App f (Suc (Var p))))
  wnf_enter e s (App (Gua fn sc) n)

wnf_app_gua_get :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_get e s f (Get c) a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Gua f0 (Get c0)) x) (App (Gua f1 (Get c1)) y))
  Tup x y -> do
    inc_inters e
    xV <- fresh e
    yV <- fresh e
    let fn = Lam xV (Lam yV (App f (Tup (Var xV) (Var yV))))
    wnf_enter e s (App (App (Gua fn c) x) y)
  Gua {} -> do
    wnf_app_gua_gua e s f (Get c) a
  _ -> wnf_unwind e s (App (Gua f (Get c)) a)

wnf_app_gua_efq :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_efq e s f Efq a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    wnf_enter e s (Sup l (App (Gua f0 Efq) x) (App (Gua f1 Efq) y))
  Gua {} -> do
    wnf_app_gua_gua e s f Efq a
  _ -> wnf_unwind e s (App (Gua f Efq) a)

wnf_app_gua_use :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_use e s f (Use u) a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (u0, u1) <- clone e l u
    wnf_enter e s (Sup l (App (Gua f0 (Use u0)) x) (App (Gua f1 (Use u1)) y))
  One -> do
    inc_inters e
    wnf_enter e s (Gua (App f One) u)
  Gua {} -> do
    wnf_app_gua_gua e s f (Use u) a
  _ -> wnf_unwind e s (App (Gua f (Use u)) a)

wnf_app_gua_if :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_if e s f (If ft ff) a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (ft0, ft1) <- clone e l ft
    (ff0, ff1) <- clone e l ff
    wnf_enter e s (Sup l (App (Gua f0 (If ft0 ff0)) x) (App (Gua f1 (If ft1 ff1)) y))
  Fal -> do
    inc_inters e
    wnf_enter e s (Gua (App f Fal) ft)
  Tru -> do
    inc_inters e
    wnf_enter e s (Gua (App f Tru) ff)
  Gua {} -> do
    wnf_app_gua_gua e s f (If ft ff) a
  _ -> wnf_unwind e s (App (Gua f (If ft ff)) a)

wnf_app_gua_mat :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_app_gua_mat e s f (Mat n c) a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (n0, n1) <- clone e l n
    (c0, c1) <- clone e l c
    wnf_enter e s (Sup l (App (Gua f0 (Mat n0 c0)) x) (App (Gua f1 (Mat n1 c1)) y))
  Nil -> do
    inc_inters e
    wnf_enter e s (Gua (App f Nil) n)
  Con h t -> do
    inc_inters e
    hV <- fresh e
    tV <- fresh e
    let fn = Lam hV (Lam tV (App f (Con (Var hV) (Var tV))))
    wnf_enter e s (App (App (Gua fn c) h) t)
  Gua {} -> do
    wnf_app_gua_gua e s f (Mat n c) a
  _ -> wnf_unwind e s (App (Gua f (Mat n c)) a)
