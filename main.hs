-- Calculus of Interactions
-- ========================
-- CoI is a term rewrite system for the following grammar:
--
-- Term ::=
-- | Var ::= Name
-- | Dp0 ::= Name "₀"
-- | Dp1 ::= Name "₁"
-- | Ref ::= "@" Name
-- | Nam ::= "." Name
-- | Dry ::= "." "(" Term " " Term ")"
-- | Era ::= "&{}"
-- | Sup ::= "&" Name "{" Term "," Term "}"
-- | Dup ::= "!" Name "&" Name "=" Term ";" Term
-- | Set ::= "*"
-- | All ::= "∀" Term "." Term
-- | Lam ::= "λ" Name "." Term
-- | App ::= "(" Term " " Term ")"
-- | Sig ::= "Σ" Term "." Term
-- | Tup ::= Term "," Term
-- | Get ::= "λ" "{" "," ":" Term ";"? "}"
-- | Emp ::= "⊥"
-- | Efq ::= "λ" "{" "}"
-- | Uni ::= "⊤"
-- | One ::= "()"
-- | Use ::= "λ" "{" "()" ":" Term ";"? "}"
-- | Bol ::= "𝔹"
-- | Fal ::= "#F"
-- | Tru ::= "#T"
-- | If  ::= "λ" "{" "#F" ":" Term ";"? "#T" ":" Term ";"? "}"
-- | Nat ::= "ℕ"
-- | Zer ::= "0"
-- | Suc ::= "1+"
-- | Swi ::= "λ" "{" "0" ":" Term ";"? "1" "+" ":" Term ";"? "}"
-- | Lst ::= Term "[]"
-- | Nil ::= "[]"
-- | Con ::= Term "<>" Term
-- | Mat ::= "λ" "{" "[]" ":" Term ";"? "<>" Term ";"? "}"
-- | And ::= Term "&&" Term
-- | Eql ::= Term "==" Term
-- | Gua ::= Term "~>" Term
--
-- Where:
-- - Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $
-- - [T]  ::= any sequence of T separated by ","
--
-- In CoI:
-- - Variables are affine (they must occur at most once)
-- - Variables range globally (they can occur anywhere)
--
-- Reference Interaction
-- =====================
--
-- @foo
-- ---------------------- ref
-- foo ~> alloc(book.foo)
--
-- Duplication Interactions
-- ========================
--
-- ! X &L = &{}
-- ------------ dup-era
-- X₀ ← &{}
-- X₁ ← &{}
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
-- ! X &L = *
-- ---------- dup-set
-- X₀ ← *
-- X₁ ← *
--
-- ! X &L = ∀a.b
-- ------------- dup-all
-- ! A &L = a
-- ! B &L = b
-- X₀ ← ∀A₀.B₀
-- X₁ ← ∀A₁.B₁
--
-- ! F &L = λx.f
-- ---------------- dup-lam
-- F₀ ← λ$x0.G₀
-- F₁ ← λ$x1.G₁
-- x  ← &L{$x0,$x1}
-- ! G &L = f
--
-- ! X &L = Σa.b
-- ------------- dup-sig (NEW)
-- ! A &L = a
-- ! B &L = b
-- X₀ ← ΣA₀.B₀
-- X₁ ← ΣA₁.B₁
--
-- ! X &L = (a,b)
-- -------------- dup-tup (NEW)
-- ! A &L = a
-- ! B &L = b
-- X₀ ← (A₀,B₀)
-- X₁ ← (A₁,B₁)
--
-- ! X &L = λ{,:c}
-- --------------- dup-get (NEW)
-- ! C &L = c
-- X₀ ← λ{,:C₀}
-- X₁ ← λ{,:C₁}
--
-- ! X &L = ⊥
-- ---------- dup-emp (NEW)
-- X₀ ← ⊥
-- X₁ ← ⊥
--
-- ! X &L = λ{}
-- ------------ dup-efq (NEW)
-- X₀ ← λ{}
-- X₁ ← λ{}
--
-- ! X &L = ⊤
-- ---------- dup-uni (NEW)
-- X₀ ← ⊤
-- X₁ ← ⊤
--
-- ! X &L = ()
-- ----------- dup-one (NEW)
-- X₀ ← ()
-- X₁ ← ()
--
-- ! X &L = λ{():u}
-- ---------------- dup-use (NEW)
-- ! U &L = u
-- X₀ ← λ{():U₀}
-- X₁ ← λ{():U₁}
--
-- ! X &L = 𝔹
-- ---------- dup-bol (NEW)
-- X₀ ← 𝔹
-- X₁ ← 𝔹
--
-- ! X &L = #F
-- ----------- dup-fal (NEW)
-- X₀ ← #F
-- X₁ ← #F
--
-- ! X &L = #T
-- ----------- dup-tru (NEW)
-- X₀ ← #T
-- X₁ ← #T
--
-- ! X &L = λ{#F:f;#T:t}
-- --------------------- dup-if (NEW)
-- ! F &L = f
-- ! T &L = t
-- X₀ ← λ{#F:F₀;#T:T₀}
-- X₁ ← λ{#F:F₁;#T:T₁}
--
-- ! X &L = ℕ
-- ---------- dup-nat
-- X₀ ← ℕ
-- X₁ ← ℕ
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
-- ! X &L = t[]
-- ------------ dup-lst (NEW)
-- ! T &L = t
-- X₀ ← T₀[]
-- X₁ ← T₁[]
--
-- ! X &L = []
-- ----------- dup-nil (NEW)
-- X₀ ← []
-- X₁ ← []
--
-- ! X &L = h<>t
-- ------------- dup-con (NEW)
-- ! H &L = h
-- ! T &L = t
-- X₀ ← H₀<>T₀
-- X₁ ← H₁<>T₁
--
-- ! X &L = λ{[]:n;<>:c}
-- --------------------- dup-mat (NEW)
-- ! N &L = n
-- ! C &L = c
-- X₀ ← λ{[]:N₀;<>:C₀}
-- X₁ ← λ{[]:N₁;<>:C₁}
--
-- ! X &L = .n
-- ----------- dup-nam
-- X₀ ← .n
-- X₁ ← .n
--
-- ! X &L = .(f x)
-- --------------- dup-dry
-- ! F &L = f
-- ! A &L = x
-- X₀ ← .(F₀ A₀)
-- X₁ ← .(F₁ A₁)
--
-- ! X &L = f ~> g
-- --------------- dup-gua
-- ! F &L = f
-- ! G &L = g
-- X₀ ← F₀ ~> G₀
-- X₁ ← F₁ ~> G₁
--
-- Application Interactions
-- ========================
--
-- (&{} a)
-- ------- app-era
-- &{}
--
-- (&L{f,g} a)
-- ----------------- app-sup
-- ! A &L = a
-- &L{(f A₀),(g A₁)}
--
-- (λx.f a)
-- -------- app-lam
-- x ← a
-- f
--
-- (λ{,:c} &{})
-- ------------ app-get-era (NEW)
-- &{}
--
-- (λ{,:c} &L{a,b})
-- ---------------- app-get-sup (NEW)
-- ! C &L = c
-- &L{(λ{,:C₀} a)
--   ,(λ{,:C₁} b)}
--
-- (λ{,:c} (a,b))
-- -------------- app-get-tup (NEW)
-- (c a b)
--
-- (λ{} &{})
-- --------- app-efq-era (NEW)
-- &{}
--
-- (λ{} &L{a,b})
-- ------------- app-efq-sup (NEW)
-- &L{(λ{} a)
--   ,(λ{} b)}
--
-- (λ{} ⊥)
-- ------- app-efq-emp (NEW)
-- λ{} ⊥
--
-- (λ{():u} &{})
-- ------------- app-use-era (NEW)
-- &{}
--
-- (λ{():u} &L{a,b})
-- ----------------- app-use-sup (NEW)
-- ! U &L = u
-- &L{(λ{():U₀} a)
--   ,(λ{():U₁} b)}
--
-- (λ{():u} ())
-- ------------ app-use-one (NEW)
-- u
--
-- (λ{#F:f;#T:t} &{})
-- ------------------ app-if-era (NEW)
-- &{}
--
-- (λ{#F:f;#T:t} &L{a,b})
-- ---------------------- app-if-sup (NEW)
-- ! F &L = f
-- ! T &L = t
-- &L{(λ{#F:F₀;#T:T₀} a)
--   ,(λ{#F:F₁;#T:T₁} b)}
--
-- (λ{#F:f;#T:t} #F)
-- ----------------- app-if-fal (NEW)
-- f
--
-- (λ{#F:f;#T:t} #T)
-- ----------------- app-if-tru (NEW)
-- t
--
-- (Λ{0:z;1+:s} &{})
-- ----------------- app-swi-era
-- &{}
--
-- (Λ{0:z;1+:s} &L{a,b})
-- --------------------- app-swi-sup
-- ! Z &L = z
-- ! S &L = s
-- &L{(Λ{0:Z₀;1+:S₀} a)
--   ,(Λ{0:Z₁;1+:S₁} b)}
--
-- (Λ{0:z;1+:s} 0)
-- --------------- app-swi-zer
-- z
--
-- (Λ{0:z;1+:s} 1+n)
-- ----------------- app-swi-suc
-- (s n)
--
-- (λ{[]:n;<>:c} &{})
-- ------------------ app-mat-era (NEW)
-- &{}
--
-- (λ{[]:n;<>:c} &L{a,b})
-- ---------------------- app-mat-sup (NEW)
-- ! N &L = n
-- ! C &L = c
-- &L{(λ{[]:N₀;<>:C₀} a)
--   ,(λ{[]:N₁;<>:C₁} b)}
--
-- (λ{[]:n;<>:c} [])
-- ----------------- app-mat-nil (NEW)
-- n
--
-- (λ{[]:n;<>:c} h<>t)
-- ------------------- app-mat-con (NEW)
-- (c h t)
--
-- (.n a)
-- ------ app-nam
-- .(.n a)
--
-- (.(f x) a)
-- ---------- app-dry
-- .(.(f x) a)
--
-- Conjunction Interactions
-- ========================
--
-- &{} && b
-- -------- and-era
-- &{}
--
-- &L{a0,a1} && b
-- -------------- and-sup
-- ! B &L = b
-- &L{B₀ && a0
--   ,B₁ && a1}
--
-- #F && b
-- ------- and-fal (NEW - now uses #F instead of 0)
-- #F
--
-- #T && b
-- ------- and-tru (NEW - now uses #T instead of 1)
-- b
--
-- Equality Interactions
-- =====================
--
-- &{} == b
-- -------- eql-era-any
-- &{}
--
-- &L{a0,a1} == b
-- -------------- eql-sup-any
-- ! &L B = b
-- &L{a0 == B₀
--   ,a1 == B₁}
--
-- a == &{}
-- -------- eql-any-era
-- &{}
--
-- a == &L{b0,b1}
-- -------------- eql-any-sup
-- ! &L A = a
-- &L{A₀ == b0
--   ,A₁ == b1}
--
-- * == *
-- ------ eql-set-set
-- 1
--
-- ∀aA.aB == ∀bA.bB
-- ------------------ eql-all-all
-- (aA==bA)&&(aB==bB)
--
-- λax.af == λbx.bf
-- ---------------- eql-lam-lam
-- ax ← X
-- bx ← X
-- af == bf
--
-- ΣaA.aB == ΣbA.bB
-- ---------------- eql-sig-sig
-- (aA==bA)&&(aB==bB)
--
-- (a1,a2) == (b1,b2)
-- ------------------ eql-tup-tup
-- (a1==b1)&&(a2==b2)
-- 
-- λ{,:ac} == λ{,:bc}
-- ------------------ eql-get-get
-- ac == bc
--
-- ⊥ == ⊥
-- ------ eql-emp-emp
-- 1
--
-- λ{} == λ{}
-- ---------- eql-efq-efq
-- 1
--
-- ⊤ == ⊤
-- ------ eql-uni-uni
-- 1
--
-- () == ()
-- -------- eql-one-one
-- 1
--
-- λ{():au} == λ{():bu}
-- -------------------- eql-use-use
-- au == bu
--
-- 𝔹 == 𝔹
-- ------ eql-bol-bol
-- 1
--
-- #F == #F
-- -------- eql-fal-fal
-- 1
--
-- #T == #T
-- -------- eql-tru-tru
-- 1
--
-- #F == #T
-- -------- eql-fal-tru
-- 0
--
-- #T == #F
-- -------- eql-tru-fal
-- 0
--
-- λ{#F:af;#T:at} == λ{#F:bf;#T:bt}
-- ------------------------------- eql-if-if
-- (af==bf)&&(at==bt)
--
-- ℕ == ℕ
-- ------ eql-nat-nat
-- 1
--
-- 0 == 0
-- ------ eql-zer-zer
-- 1
--
-- 1+a == 1+b
-- ---------- eql-suc-suc
-- a == b
--
-- Λ{0:az;1+:as} == Λ{0:bz;1+:bs}
-- ------------------------------ eql-swi-swi
-- (az==bz)&&(as==bs)
--
-- aT[] == bT[]
-- ------------ eql-lst-lst
-- aT == bT
--
-- [] == []
-- -------- eql-nil-nil
-- 1
--
-- ah<>at == bh<>bt
-- ---------------- eql-con-con
-- (ah==bh)&&(at==bt)
--
-- λ{[]:an;<>:ac} == λ{[]:bn;<>:bc}
-- --------------------------------- eql-mat-mat
-- (an==bn)&&(ac==bc)
--
-- .x == .y
-- ---------- eql-nam-nam
-- if x == y:
--   1
-- else:
--   0
--
-- .(af ax) == .(bf bx)
-- ------------------------ eql-dry-dry
-- (af == bf) && (ax == bx)
--
-- (af~>ag) == b
-- ------------- eql-gua
-- TODO
--
-- Guarded Application Interactions
-- ================================
--
-- ((f ~> &{}) a)
-- -------------- app-gua-era
-- &{}
--
-- ((f ~> &L{x,y}) a)
-- ------------------ app-gua-sup
-- ! &L F = f
-- ! F &L = f
-- ! A &L = a
-- &L{((F₀ ~> x) A₀)
--   ,((F₁ ~> y) A₁)}
--
-- ((f ~> λx.g) a)
-- --------------- app-gua-lam
-- x ← a
-- (f x) ~> g
--
-- ((f ~> λ{,:c}) &{})
-- ------------------- app-gua-get-era (NEW)
-- &{}
--
-- ((f ~> λ{,:c}) &L{a,b})
-- ----------------------- app-gua-get-sup (NEW)
-- ! F &L = f
-- ! C &L = c
-- &L{((F₀ ~> λ{,:C₀}) a)
--   ,((F₁ ~> λ{,:C₁}) b)}
--
-- ((f ~> λ{,:c}) (a,b))
-- ---------------------------- app-gua-get-tup (NEW)
-- ((λx.λy.(f (x,y)) ~> c) a b)
--
-- ((f ~> λ{}) &{})
-- ---------------- app-gua-efq-era (NEW)
-- &{}
--
-- ((f ~> λ{}) &L{a,b})
-- -------------------- app-gua-efq-sup (NEW)
-- ! F &L = f
-- &L{((F₀ ~> λ{}) a)
--   ,((F₁ ~> λ{}) b)}
--
-- ((f ~> λ{():u}) &{})
-- -------------------- app-gua-use-era (NEW)
-- &{}
--
-- ((f ~> λ{():u}) &L{a,b})
-- ------------------------ app-gua-use-sup (NEW)
-- ! F &L = f
-- ! U &L = u
-- &L{((F₀ ~> λ{():U₀}) a)
--   ,((F₁ ~> λ{():U₁}) b)}
--
-- ((f ~> λ{():u}) ())
-- ------------------- app-gua-use-one (NEW)
-- (f ()) ~> u
--
-- ((g ~> λ{#F:f;#T:t}) &{})
-- ------------------------- app-gua-if-era (NEW)
-- &{}
--
-- ((g ~> λ{#F:f;#T:t}) &L{a,b})
-- ------------------------------- app-gua-if-sup (NEW)
-- ! G &L = g
-- ! F &L = f
-- ! T &L = t
-- &L{((G₀ ~> λ{#F:F₀;#T:T₀}) a)
--   ,((G₁ ~> λ{#F:F₁;#T:T₁}) b)}
--
-- ((g ~> λ{#F:f;#T:t}) #F)
-- ------------------------ app-gua-if-fal (NEW)
-- (g #F) ~> f
--
-- ((g ~> λ{#F:f;#T:t}) #T)
-- ------------------------ app-gua-if-tru (NEW)
-- (g #T) ~> t
--
-- ((f ~> λ{[]:n;<>:c}) &{})
-- ------------------------- app-gua-mat-era (NEW)
-- &{}
--
-- ((f ~> λ{[]:n;<>:c}) &L{a,b})
-- ----------------------------- app-gua-mat-sup (NEW)
-- ! F &L = f
-- ! N &L = n
-- ! C &L = c
-- &L{((F₀ ~> λ{[]:N₀;<>:C₀}) a)
--   ,((F₁ ~> λ{[]:N₁;<>:C₁}) b)}
--
-- ((f ~> λ{[]:n;<>:c}) [])
-- ------------------------ app-gua-mat-nil (NEW)
-- (f []) ~> n
--
-- ((f ~> λ{[]:n;<>:c}) h<>t)
-- -------------------------- app-gua-mat-con (NEW)
-- ((λh.λt.(f h<>t) ~> c) h t)
--
-- ((f ~> Λ{0:z;1+:s}) &{})
-- ------------------------ app-gua-swi-era
-- &{}
--
-- ((f ~> Λ{0:z;1+:s}) &L{a,b})
-- ---------------------------- app-gua-swi-sup
-- ! F &L = f
-- ! Z &L = z
-- ! S &L = s
-- &L{((F₀ ~> Λ{0:Z₀;1+:S₀}) a)
--   ,((F₁ ~> Λ{0:Z₁;1+:S₁}) b)}
--
-- ((f ~> Λ{0:z;1+:s}) 0)
-- ---------------------- app-gua-swi-zer
-- (f 0) ~> z
--
-- ((f ~> Λ{0:z;1+:s}) 1+n)
-- ------------------------ app-gua-swi-suc
-- ((λp.(f 1+p) ~> s) n)

{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -O2 #-}

import Control.Monad (forM_)
import Data.Bits (shiftL)
import Data.Char (isDigit)
import Data.IORef
import Data.List (foldl', elemIndex)
import System.CPUTime
import Text.ParserCombinators.ReadP
import Text.Printf
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
  | Ref !Name
  | Nam !String
  | Dry !Term !Term
  | Era
  | Sup !Lab !Term !Term
  | Dup !Name !Lab !Term !Term
  | Set
  | All !Term !Term
  | Lam !Name !Term
  | App !Term !Term
  | Sig !Term !Term
  | Tup !Term !Term
  | Get !Term
  | Emp
  | Efq
  | Uni
  | One
  | Use !Term
  | Bol
  | Fal
  | Tru
  | If !Term !Term
  | Nat
  | Zer
  | Suc !Term
  | Swi !Term !Term
  | Lst !Term
  | Nil
  | Con !Term !Term
  | Mat !Term !Term
  | And !Term !Term
  | Eql !Term !Term
  | Gua !Term !Term
  deriving (Eq)

data Kind
  = VAR
  | DP0
  | DP1
  deriving (Enum)

data Book = Book (M.Map Name Term)

data Env = Env
  { env_book    :: !Book
  , env_inters  :: !(IORef Int)
  , env_new_id  :: !(IORef Int)
  , env_sub_map :: !(IORef (IM.IntMap Term))
  , env_dup_map :: !(IORef (IM.IntMap (Lab, Term)))
  }

-- Showing
-- =======

instance Show Term where
  show (Var k)       = int_to_name k
  show (Dp0 k)       = int_to_name k ++ "₀"
  show (Dp1 k)       = int_to_name k ++ "₁"
  show (Ref k)       = "@" ++ int_to_name k
  show (Nam k)       = "" ++ k
  show (Dry f x)     = show_app f [x]
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ int_to_name l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ int_to_name k ++ "&" ++ int_to_name l ++ "=" ++ show v ++ ";" ++ show t
  show Set           = "*"
  show (All a b)     = "∀" ++ show a ++ "." ++ show b
  show (Lam k f)     = "λ" ++ int_to_name k ++ "." ++ show f
  show (App f x)     = show_app f [x]
  show (Sig a b)     = "Σ" ++ show a ++ "." ++ show b
  show (Tup a b)     = "(" ++ show a ++ "," ++ show b ++ ")"
  show (Get c)       = "λ{,:" ++ show c ++ "}"
  show Emp           = "⊥"
  show Efq           = "λ{}"
  show Uni           = "⊤"
  show One           = "()"
  show (Use u)       = "λ{():" ++ show u ++ "}"
  show Bol           = "𝔹"
  show Fal           = "#F"
  show Tru           = "#T"
  show (If f t)      = "λ{#F:" ++ show f ++ ";#T:" ++ show t ++ "}"
  show Nat           = "ℕ"
  show Zer           = "0"
  show (Suc p)       = show_add 1 p
  show (Swi z s)     = "λ{0:" ++ show z ++ ";1+:" ++ show s ++ "}"
  show (Lst t)       = show t ++ "[]"
  show Nil           = "[]"
  show (Con h t)     = show h ++ "<>" ++ show t
  show (Mat n c)     = "λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (And a b)     = show a ++ "&&" ++ show b
  show (Eql a b)     = show a ++ "==" ++ show b
  show (Gua f g)     = show f ++ "~>" ++ show g

show_add :: Int -> Term -> String
show_add n Zer     = show n
show_add n (Suc p) = show_add (n + 1) p
show_add n term    = show n ++ "+" ++ show term

show_app :: Term -> [Term] -> String
show_app (Dry f x) args = show_app f (x : args)
show_app (App f x) args = show_app f (x : args)
show_app f         args = "(" ++ unwords (map show (f : args)) ++ ")"

instance Show Book where
  show (Book m) = unlines [ "@" ++ int_to_name k ++ " = " ++ show ct | (k, ct) <- M.toList m ]

show_dup_map :: IM.IntMap (Lab, Term) -> String
show_dup_map m = unlines [ "! " ++ int_to_name k ++ " &" ++ int_to_name l ++ " = " ++ show v | (k, (l, v)) <- IM.toList m ]

show_sub_map :: IM.IntMap Term -> String
show_sub_map m = unlines [ int_to_name (k `div` 4) ++ suffix (k `mod` 4) ++ " ← " ++ show v | (k, v) <- IM.toList m ]
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
int_to_name 0 = "_"
int_to_name n = reverse (go n)
  where go 0 = ""
        go m = let (q,r) = m `divMod` 64 in alphabet !! r : go q

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

parse_nam :: ReadP String
parse_nam = lexeme $ do
  head <- satisfy (`elem` alphabet_first)
  tail <- munch (`elem` alphabet)
  return (head : tail)

parse_term :: ReadP Term
parse_term = do
  t <- parse_term_base
  parse_term_suff t

parse_term_suff :: Term -> ReadP Term
parse_term_suff t = skipSpaces >> choice
  [ do string "&&"; t2 <- parse_term; return (And t t2)
  , do string "=="; t2 <- parse_term; return (Eql t t2)
  , do string "~>"; t2 <- parse_term; return (Gua t t2)
  , do string "[]"; t' <- return (Lst t); parse_term_suff t'
  , do string "<>"; t2 <- parse_term; return (Con t t2)
  , return t
  ]

parse_term_base :: ReadP Term
parse_term_base = lexeme $ choice
  [ parse_lam_or_swi
  , parse_dup
  , parse_par
  , parse_sup
  , parse_era
  , parse_set
  , parse_all
  , parse_sig
  , parse_nat
  , parse_add
  , parse_num
  , parse_ref
  , parse_emp
  , parse_uni
  , parse_bol
  , parse_ctr
  , parse_nil
  , parse_var
  ]

parse_par :: ReadP Term
parse_par = do
  lexeme (char '(')
  choice
    [ do lexeme (char ')'); return One
    , do
      t <- parse_term
      choice
        [ do lexeme (char ','); u <- parse_term; lexeme (char ')'); return (Tup t u)
        , do ts <- many parse_term; lexeme (char ')'); return (foldl' App t ts)
        ]
    ]

parse_lam_or_swi :: ReadP Term
parse_lam_or_swi = do
  lexeme (choice [char 'λ', char '\\'])
  parse_lam_brace <++ parse_lam_body

parse_lam_body :: ReadP Term
parse_lam_body = do
  k <- parse_nam
  lexeme (char '.')
  body <- parse_term
  return (Lam (name_to_int k) body)

parse_lam_brace :: ReadP Term
parse_lam_brace = between (lexeme (char '{')) (lexeme (char '}')) $ choice
  [ do lexeme (string "0:"); z <- parse_term; optional (lexeme (char ';')); lexeme (string "1+:"); s <- parse_term; return (Swi z s)
  , do lexeme (string "[]:"); n <- parse_term; optional (lexeme (char ';')); lexeme (string "<>:"); c <- parse_term; return (Mat n c)
  , do lexeme (string "#F:"); f <- parse_term; optional (lexeme (char ';')); lexeme (string "#T:"); t <- parse_term; return (If f t)
  , do lexeme (string "():"); u <- parse_term; return (Use u)
  , do lexeme (string ",:"); c <- parse_term; return (Get c)
  , return Efq
  ]

parse_dup :: ReadP Term
parse_dup = do
  lexeme (char '!')
  k <- parse_nam
  lexeme (char '&')
  l <- parse_nam
  lexeme (char '=')
  v <- parse_term
  optional (lexeme (char ';'))
  t <- parse_term
  return (Dup (name_to_int k) (name_to_int l) v t)

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- parse_nam
  between (lexeme (char '{')) (lexeme (char '}')) $ do
    a <- parse_term
    optional (lexeme (char ','))
    b <- parse_term
    return (Sup (name_to_int l) a b)

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_set :: ReadP Term
parse_set = lexeme (char '*') >> return Set

parse_all :: ReadP Term
parse_all = do
  lexeme (char '∀')
  a <- parse_term_base
  lexeme (char '.')
  b <- parse_term
  return (All a b)

parse_sig :: ReadP Term
parse_sig = do
  lexeme (char 'Σ')
  a <- parse_term_base
  lexeme (char '.')
  b <- parse_term
  return (Sig a b)

parse_nat :: ReadP Term
parse_nat = lexeme (char 'ℕ') >> return Nat

parse_ref :: ReadP Term
parse_ref = do
  lexeme (char '@')
  k <- parse_nam
  return (Ref (name_to_int k))

parse_add :: ReadP Term
parse_add = do
  value <- parse_number
  skipSpaces
  _ <- char '+'
  term <- parse_term_base
  return (iterate Suc term !! value)

parse_num :: ReadP Term
parse_num = do
  value <- parse_number
  return (iterate Suc Zer !! value)

parse_number :: ReadP Int
parse_number = read <$> munch1 isDigit

parse_var :: ReadP Term
parse_var = do
  k <- parse_nam
  let kid = name_to_int k
  choice
    [ string "₀" >> return (Dp0 kid)
    , string "₁" >> return (Dp1 kid)
    , return (Var kid)
    ]

parse_emp :: ReadP Term
parse_emp = lexeme (char '⊥') >> return Emp

parse_uni :: ReadP Term
parse_uni = lexeme (char '⊤') >> return Uni

parse_bol :: ReadP Term
parse_bol = lexeme (char '𝔹') >> return Bol

parse_ctr :: ReadP Term
parse_ctr = do
  lexeme (char '#')
  choice
    [ char 'F' >> return Fal
    , char 'T' >> return Tru
    ]

parse_nil :: ReadP Term
parse_nil = do
  lexeme (char '[')
  lexeme (char ']')
  return Nil

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

new_env :: Book -> IO Env
new_env bk = do
  itr <- newIORef 0
  ids <- newIORef 1
  sub <- newIORef IM.empty
  dm  <- newIORef IM.empty
  return $ Env bk itr ids sub dm

inc_inters :: Env -> IO ()
inc_inters e = do
  !n <- readIORef (env_inters e)
  writeIORef (env_inters e) (n + 1)

fresh :: Env -> IO Name
fresh e = do
  !n <- readIORef (env_new_id e)
  writeIORef (env_new_id e) (n + 1)
  return ((n `shiftL` 6) + 63)

taker :: IORef (IM.IntMap a) -> Int -> IO (Maybe a)
taker ref k = do
  !m <- readIORef ref
  case IM.lookup k m of
    Nothing -> do
      return Nothing
    Just v  -> do
      writeIORef ref (IM.delete k m)
      return (Just v)

take_dup :: Env -> Name -> IO (Maybe (Lab, Term))
take_dup e k = taker (env_dup_map e) k

take_sub :: Kind -> Env -> Name -> IO (Maybe Term)
take_sub ki e k = taker (env_sub_map e) (k `shiftL` 2 + fromEnum ki)

make_dup :: Env -> Name -> Lab -> Term -> IO ()
make_dup e k l v = modifyIORef' (env_dup_map e) (IM.insert k (l, v))

make_auto_dup :: Env -> Name -> Lab -> Term -> IO ()
make_auto_dup e k l v = do { k <- fresh e ; make_dup e k l v }

subst :: Kind -> Env -> Name -> Term -> IO ()
subst s e k v = modifyIORef' (env_sub_map e) (IM.insert (k `shiftL` 2 + fromEnum s) v)

-- Cloning
-- =======

clone :: Env -> Lab -> Term -> IO (Term, Term)
clone e l v = do
  k <- fresh e
  make_dup e k l v
  return $ (Dp0 k , Dp1 k)

clone_list :: Env -> Lab -> [Term] -> IO ([Term],[Term])
clone_list e l []       = return $ ([],[])
clone_list e l (x : xs) = do
  (x0  , x1 ) <- clone e l x
  (xs0 , xs1) <- clone_list e l xs
  return $ (x0 : xs0 , x1 : xs1)

-- WNF: Weak Normal Form
-- =====================

-- now, complete with the rest of the file below:

data Frame
  = FDp0   Name Lab -- ! F &L = _; F₀
  | FDp1   Name Lab -- ! F &L = _; F₁
  | FApp   Term     -- (f x)
  | FAppF  Term     -- (λ{..} x)
  | FAppG  Term     -- ((f~>g) x)
  | FAppGF Term     -- ((f~>λ{..}) x)
  | FAnd   Term     -- (a && b)
  | FEql   Term     -- (a == b)
  | FEqlA  Term     -- (a == b) where a is an introducer

type Stack = [Frame]

wnf :: Env -> Stack -> Term -> IO Term
wnf = wnf_enter

-- WNF: Enter
-- ----------

wnf_enter :: Env -> Stack -> Term -> IO Term

wnf_enter e s (Var k) = do
  wnf_sub VAR e s k

wnf_enter e s (Dp0 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp0 k l : s) v
    Nothing     -> wnf_sub DP0 e s k

wnf_enter e s (Dp1 k) = do
  mlv <- take_dup e k
  case mlv of
    Just (l, v) -> wnf_enter e (FDp1 k l : s) v
    Nothing     -> wnf_sub DP1 e s k

wnf_enter e s (App f x) = do
  wnf_enter e (FApp x : s) f

wnf_enter e s (And a b) = do
  wnf_enter e (FAnd b : s) a

wnf_enter e s (Eql a b) = do
  wnf_enter e (FEql b : s) a

wnf_enter e s (Dup k l v t) = do
  make_dup e k l v
  wnf_enter e s t

wnf_enter e s (Ref k) = do
  let (Book m) = env_book e
  case M.lookup k m of
    Just f  -> do
      inc_inters e
      g <- alloc e f
      wnf_enter e s (Gua (Nam ("@" ++ int_to_name k)) g)
    Nothing -> error $ "UndefinedReference: " ++ int_to_name k

wnf_enter e s (Gua f g) = do
  wnf_unwind e s (Gua f g)

wnf_enter e s f = do
  wnf_unwind e s f

-- WNF: Unwind
-- -----------

wnf_unwind :: Env -> Stack -> Term -> IO Term
wnf_unwind e []      v = return v
wnf_unwind e (x : s) v = do
  case x of
    FApp a           -> wnf_app e s v a
    FDp0 k l         -> wnf_dup e s v k l (Dp0 k)
    FDp1 k l         -> wnf_dup e s v k l (Dp1 k)
    FAnd b           -> wnf_and e s v b
    FEql b           -> wnf_enter e (FEqlA v : s) b
    FEqlA a          -> wnf_eql e s a v
    FAppF f          -> wnf_appf e s f v
    FAppG (Tup f a)  -> wnf_appg e s f v a
    FAppGF (Tup f m) -> wnf_appgf e s f m v
    _                -> error "BadFrame"

-- WNF: Sub Interaction
-- --------------------

wnf_sub :: Kind -> Env -> Stack -> Name -> IO Term
wnf_sub ki e s k = do
  mt <- take_sub ki e k
  case mt of
    Just t  -> wnf e s t
    Nothing -> wnf_unwind e s $ case ki of
      VAR -> Var k
      DP0 -> Dp0 k
      DP1 -> Dp1 k

-- WNF: Dup Interactions
-- ---------------------

type WnfDup = Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term

wnf_dup :: Env -> Stack -> Term -> Name -> Lab -> Term -> IO Term
wnf_dup e s v k l t = case v of
  Era    -> wnf_dup_era e s v k l t
  Sup {} -> wnf_dup_sup e s v k l t
  Set    -> wnf_dup_set e s v k l t
  All {} -> wnf_dup_all e s v k l t
  Lam {} -> wnf_dup_lam e s v k l t
  Nat    -> wnf_dup_nat e s v k l t
  Zer    -> wnf_dup_zer e s v k l t
  Suc {} -> wnf_dup_suc e s v k l t
  Swi {} -> wnf_dup_swi e s v k l t
  Nam {} -> wnf_dup_nam e s v k l t
  Dry {} -> wnf_dup_dry e s v k l t
  Gua {} -> wnf_dup_gua e s v k l t
  Sig {} -> wnf_dup_sig e s v k l t
  Tup {} -> wnf_dup_tup e s v k l t
  Get {} -> wnf_dup_get e s v k l t
  Emp    -> wnf_dup_emp e s v k l t
  Efq    -> wnf_dup_efq e s v k l t
  Uni    -> wnf_dup_uni e s v k l t
  One    -> wnf_dup_one e s v k l t
  Use {} -> wnf_dup_use e s v k l t
  Bol    -> wnf_dup_bol e s v k l t
  Fal    -> wnf_dup_fal e s v k l t
  Tru    -> wnf_dup_tru e s v k l t
  If {}  -> wnf_dup_if  e s v k l t
  Lst {} -> wnf_dup_lst e s v k l t
  Nil    -> wnf_dup_nil e s v k l t
  Con {} -> wnf_dup_con e s v k l t
  Mat {} -> wnf_dup_mat e s v k l t
  _      -> wnf_unwind e s (Dup k l v t)

wnf_dup_0 :: Env -> Stack -> Name -> Term -> Term -> IO Term
wnf_dup_0 e s k v t = do
  inc_inters e
  subst DP0 e k v
  subst DP1 e k v
  wnf e s t

wnf_dup_1 :: Env -> Stack -> Name -> Lab -> Term -> Term -> (Term -> Term) -> IO Term
wnf_dup_1 e s k l t v1 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  subst DP0 e k (c v1a)
  subst DP1 e k (c v1b)
  wnf e s t

wnf_dup_2 :: Env -> Stack -> Name -> Lab -> Term -> Term -> Term -> (Term -> Term -> Term) -> IO Term
wnf_dup_2 e s k l t v1 v2 c = do
  inc_inters e
  (v1a, v1b) <- clone e l v1
  (v2a, v2b) <- clone e l v2
  subst DP0 e k (c v1a v2a)
  subst DP1 e k (c v1b v2b)
  wnf e s t

wnf_dup_era :: WnfDup
wnf_dup_era e s Era k _ t = wnf_dup_0 e s k Era t

wnf_dup_sup :: WnfDup
wnf_dup_sup e s (Sup vl va vb) k l t
  | l == vl = do
      inc_inters e
      subst DP0 e k va
      subst DP1 e k vb
      wnf e s t
  | otherwise = do
      wnf_dup_2 e s k l t va vb (Sup vl)

wnf_dup_set :: WnfDup
wnf_dup_set e s Set k _ t = wnf_dup_0 e s k Set t

wnf_dup_all :: WnfDup
wnf_dup_all e s (All va vb) k l t = wnf_dup_2 e s k l t va vb All

wnf_dup_lam :: WnfDup
wnf_dup_lam e s (Lam vk vf) k l t = do
  inc_inters e
  x0      <- fresh e
  x1      <- fresh e
  (g0,g1) <- clone e l vf
  subst DP0 e k (Lam x0 g0)
  subst DP1 e k (Lam x1 g1)
  subst VAR e vk (Sup l (Var x0) (Var x1))
  wnf e s t

wnf_dup_nat :: WnfDup
wnf_dup_nat e s Nat k _ t = wnf_dup_0 e s k Nat t

wnf_dup_zer :: WnfDup
wnf_dup_zer e s Zer k _ t = wnf_dup_0 e s k Zer t

wnf_dup_suc :: WnfDup
wnf_dup_suc e s (Suc p) k l t = wnf_dup_1 e s k l t p Suc

wnf_dup_swi :: WnfDup
wnf_dup_swi e s (Swi vz vs) k l t = wnf_dup_2 e s k l t vz vs Swi

wnf_dup_nam :: WnfDup
wnf_dup_nam e s (Nam n) k _ t = wnf_dup_0 e s k (Nam n) t

wnf_dup_dry :: WnfDup
wnf_dup_dry e s (Dry vf vx) k l t = wnf_dup_2 e s k l t vf vx Dry

wnf_dup_gua :: WnfDup
wnf_dup_gua e s (Gua f g) k l t = wnf_dup_2 e s k l t f g Gua

wnf_dup_sig :: WnfDup
wnf_dup_sig e s (Sig a b) k l t = wnf_dup_2 e s k l t a b Sig

wnf_dup_tup :: WnfDup
wnf_dup_tup e s (Tup a b) k l t = wnf_dup_2 e s k l t a b Tup

wnf_dup_get :: WnfDup
wnf_dup_get e s (Get c) k l t = wnf_dup_1 e s k l t c Get

wnf_dup_emp :: WnfDup
wnf_dup_emp e s Emp k _ t = wnf_dup_0 e s k Emp t

wnf_dup_efq :: WnfDup
wnf_dup_efq e s Efq k _ t = wnf_dup_0 e s k Efq t

wnf_dup_uni :: WnfDup
wnf_dup_uni e s Uni k _ t = wnf_dup_0 e s k Uni t

wnf_dup_one :: WnfDup
wnf_dup_one e s One k _ t = wnf_dup_0 e s k One t

wnf_dup_use :: WnfDup
wnf_dup_use e s (Use u) k l t = wnf_dup_1 e s k l t u Use

wnf_dup_bol :: WnfDup
wnf_dup_bol e s Bol k _ t = wnf_dup_0 e s k Bol t

wnf_dup_fal :: WnfDup
wnf_dup_fal e s Fal k _ t = wnf_dup_0 e s k Fal t

wnf_dup_tru :: WnfDup
wnf_dup_tru e s Tru k _ t = wnf_dup_0 e s k Tru t

wnf_dup_if :: WnfDup
wnf_dup_if e s (If f tr) k l t = wnf_dup_2 e s k l t f tr If

wnf_dup_lst :: WnfDup
wnf_dup_lst e s (Lst x) k l t = wnf_dup_1 e s k l t x Lst

wnf_dup_nil :: WnfDup
wnf_dup_nil e s Nil k _ t = wnf_dup_0 e s k Nil t

wnf_dup_con :: WnfDup
wnf_dup_con e s (Con h tr) k l t = wnf_dup_2 e s k l t h tr Con

wnf_dup_mat :: WnfDup
wnf_dup_mat e s (Mat n c) k l t = wnf_dup_2 e s k l t n c Mat

-- WNF: App Interactions
-- ---------------------

wnf_app :: Env -> Stack -> Term -> Term -> IO Term
wnf_app e s f a = case f of
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

wnf_appf :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf e s f a = case f of
  Swi {} -> wnf_appf_swi e s f a
  Get {} -> wnf_appf_get e s f a
  Efq    -> wnf_appf_efq e s f a
  Use {} -> wnf_appf_use e s f a
  If {}  -> wnf_appf_if  e s f a
  Mat {} -> wnf_appf_mat e s f a
  _      -> wnf_unwind e s (App f a)

wnf_appf_swi :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_swi e s f@(Swi z sc) a = case a of
  Era    -> wnf_appf_swi_era e s f a
  Sup {} -> wnf_appf_swi_sup e s f a
  Zer    -> wnf_appf_swi_zer e s f a
  Suc {} -> wnf_appf_swi_suc e s f a
  _      -> wnf_unwind e s (App f a)

wnf_appf_swi_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_swi_era e s (Swi z sc) Era = do
  inc_inters e
  wnf e s Era

wnf_appf_swi_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_swi_sup e s (Swi z sc) (Sup l a b) = do
  inc_inters e
  (z0, z1) <- clone e l z
  (s0, s1) <- clone e l sc
  let app0 = App (Swi z0 s0) a
  let app1 = App (Swi z1 s1) b
  wnf_enter e s (Sup l app0 app1)

wnf_appf_swi_zer :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_swi_zer e s (Swi z sc) Zer = do
  inc_inters e
  wnf e s z

wnf_appf_swi_suc :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_swi_suc e s (Swi z sc) (Suc n) = do
  inc_inters e
  wnf_enter e s (App sc n)

wnf_appf_get :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_get e s f@(Get c) a = case a of
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

wnf_appf_efq :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_efq e s Efq a = case a of
  Era -> do
    inc_inters e
    wnf e s Era
  Sup l x y -> do
    inc_inters e
    wnf_enter e s (Sup l (App Efq x) (App Efq y))
  _ -> wnf_unwind e s (App Efq a)

wnf_appf_use :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_use e s f@(Use u) a = case a of
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

wnf_appf_if :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_if e s f@(If ft ff) a = case a of
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

wnf_appf_mat :: Env -> Stack -> Term -> Term -> IO Term
wnf_appf_mat e s f@(Mat n c) a = case a of
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

-- WNF: And Interactions
-- ---------------------

wnf_and :: Env -> Stack -> Term -> Term -> IO Term
wnf_and e s a b = case a of
  Era    -> wnf_and_era e s a b
  Sup {} -> wnf_and_sup e s a b
  Fal    -> wnf_and_fal e s a b
  Tru    -> wnf_and_tru e s a b
  _      -> wnf_unwind e s (And a b)

wnf_and_era :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_era e s Era b = do
  inc_inters e
  wnf e s Era

wnf_and_sup :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_sup e s (Sup l a0 a1) b = do
  inc_inters e
  (b0, b1) <- clone e l b
  wnf_enter e s (Sup l (And a0 b0) (And a1 b1))

wnf_and_fal :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_fal e s Fal b = do
  inc_inters e
  wnf e s Fal

wnf_and_tru :: Env -> Stack -> Term -> Term -> IO Term
wnf_and_tru e s Tru b = do
  inc_inters e
  wnf e s b

-- WNF: Eql Interactions
-- ---------------------

type WnfEql = Env -> Stack -> Term -> Term -> IO Term

wnf_eql :: WnfEql
wnf_eql e s a b = case (a, b) of
  (Era, b) -> do
    inc_inters e
    wnf e s Era
  (a, Era) -> do
    inc_inters e
    wnf e s Era
  (Sup l a0 a1, b) -> do
    inc_inters e
    k <- fresh e
    make_dup e k l b
    wnf_enter e s (Sup l (Eql a0 (Dp0 k)) (Eql a1 (Dp1 k)))
  (a, Sup l b0 b1) -> do
    inc_inters e
    k <- fresh e
    make_dup e k l a
    wnf_enter e s (Sup l (Eql (Dp0 k) b0) (Eql (Dp1 k) b1))
  (a, b) -> do
    wnf_eql_val e s a b

wnf_eql_val :: WnfEql
wnf_eql_val e s a b = case (a, b) of
  (Set, Set)       -> wnf_eql_set_set e s a b
  (All {}, All {}) -> wnf_eql_all_all e s a b
  (Lam {}, Lam {}) -> wnf_eql_lam_lam e s a b
  (Sig {}, Sig {}) -> wnf_eql_sig_sig e s a b
  (Tup {}, Tup {}) -> wnf_eql_tup_tup e s a b
  (Get {}, Get {}) -> wnf_eql_get_get e s a b
  (Emp, Emp)       -> wnf_eql_emp_emp e s a b
  (Efq, Efq)       -> wnf_eql_efq_efq e s a b
  (Uni, Uni)       -> wnf_eql_uni_uni e s a b
  (One, One)       -> wnf_eql_one_one e s a b
  (Use {}, Use {}) -> wnf_eql_use_use e s a b
  (Bol, Bol)       -> wnf_eql_bol_bol e s a b
  (Fal, Fal)       -> wnf_eql_fal_fal e s a b
  (Tru, Tru)       -> wnf_eql_tru_tru e s a b
  (Fal, Tru)       -> wnf_eql_fal_tru e s a b
  (Tru, Fal)       -> wnf_eql_tru_fal e s a b
  (If {}, If {})   -> wnf_eql_if_if   e s a b
  (Nat, Nat)       -> wnf_eql_nat_nat e s a b
  (Zer, Zer)       -> wnf_eql_zer_zer e s a b
  (Suc {}, Suc {}) -> wnf_eql_suc_suc e s a b
  (Swi {}, Swi {}) -> wnf_eql_swi_swi e s a b
  (Lst {}, Lst {}) -> wnf_eql_lst_lst e s a b
  (Nil, Nil)       -> wnf_eql_nil_nil e s a b
  (Con {}, Con {}) -> wnf_eql_con_con e s a b
  (Mat {}, Mat {}) -> wnf_eql_mat_mat e s a b
  (Nam {}, Nam {}) -> wnf_eql_nam_nam e s a b
  (Dry {}, Dry {}) -> wnf_eql_dry_dry e s a b
  _                -> wnf_eql_default e s a b

wnf_eql_set_set :: WnfEql
wnf_eql_set_set e s Set Set = do
  inc_inters e
  wnf e s Tru

wnf_eql_all_all :: WnfEql
wnf_eql_all_all e s (All aA aB) (All bA bB) = do
  inc_inters e
  wnf_enter e s (And (Eql aA bA) (Eql aB bB))

wnf_eql_lam_lam :: WnfEql
wnf_eql_lam_lam e s (Lam ax af) (Lam bx bf) = do
  inc_inters e
  x <- fresh e
  subst VAR e ax (Nam (int_to_name x))
  subst VAR e bx (Nam (int_to_name x))
  wnf_enter e s (Eql af bf)

wnf_eql_sig_sig :: WnfEql
wnf_eql_sig_sig e s (Sig aA aB) (Sig bA bB) = do
  inc_inters e
  wnf_enter e s (And (Eql aA bA) (Eql aB bB))

wnf_eql_tup_tup :: WnfEql
wnf_eql_tup_tup e s (Tup a1 a2) (Tup b1 b2) = do
  inc_inters e
  wnf_enter e s (And (Eql a1 b1) (Eql a2 b2))

wnf_eql_get_get :: WnfEql
wnf_eql_get_get e s (Get ac) (Get bc) = do
  inc_inters e
  wnf_enter e s (Eql ac bc)

wnf_eql_emp_emp :: WnfEql
wnf_eql_emp_emp e s Emp Emp = do
  inc_inters e
  wnf e s Tru

wnf_eql_efq_efq :: WnfEql
wnf_eql_efq_efq e s Efq Efq = do
  inc_inters e
  wnf e s Tru

wnf_eql_uni_uni :: WnfEql
wnf_eql_uni_uni e s Uni Uni = do
  inc_inters e
  wnf e s Tru

wnf_eql_one_one :: WnfEql
wnf_eql_one_one e s One One = do
  inc_inters e
  wnf e s Tru

wnf_eql_use_use :: WnfEql
wnf_eql_use_use e s (Use au) (Use bu) = do
  inc_inters e
  wnf_enter e s (Eql au bu)

wnf_eql_bol_bol :: WnfEql
wnf_eql_bol_bol e s Bol Bol = do
  inc_inters e
  wnf e s Tru

wnf_eql_fal_fal :: WnfEql
wnf_eql_fal_fal e s Fal Fal = do
  inc_inters e
  wnf e s Tru

wnf_eql_tru_tru :: WnfEql
wnf_eql_tru_tru e s Tru Tru = do
  inc_inters e
  wnf e s Tru

wnf_eql_fal_tru :: WnfEql
wnf_eql_fal_tru e s Fal Tru = do
  inc_inters e
  wnf e s Fal

wnf_eql_tru_fal :: WnfEql
wnf_eql_tru_fal e s Tru Fal = do
  inc_inters e
  wnf e s Fal

wnf_eql_if_if :: WnfEql
wnf_eql_if_if e s (If af at) (If bf bt) = do
  inc_inters e
  wnf_enter e s (And (Eql af bf) (Eql at bt))

wnf_eql_nat_nat :: WnfEql
wnf_eql_nat_nat e s Nat Nat = do
  inc_inters e
  wnf e s Tru

wnf_eql_zer_zer :: WnfEql
wnf_eql_zer_zer e s Zer Zer = do
  inc_inters e
  wnf e s Tru

wnf_eql_suc_suc :: WnfEql
wnf_eql_suc_suc e s (Suc a) (Suc b) = do
  inc_inters e
  wnf_enter e s (Eql a b)

wnf_eql_swi_swi :: WnfEql
wnf_eql_swi_swi e s (Swi az as) (Swi bz bs) = do
  inc_inters e
  wnf_enter e s (And (Eql az bz) (Eql as bs))

wnf_eql_lst_lst :: WnfEql
wnf_eql_lst_lst e s (Lst aT) (Lst bT) = do
  inc_inters e
  wnf_enter e s (Eql aT bT)

wnf_eql_nil_nil :: WnfEql
wnf_eql_nil_nil e s Nil Nil = do
  inc_inters e
  wnf e s Tru

wnf_eql_con_con :: WnfEql
wnf_eql_con_con e s (Con ah at) (Con bh bt) = do
  inc_inters e
  wnf_enter e s (And (Eql ah bh) (Eql at bt))

wnf_eql_mat_mat :: WnfEql
wnf_eql_mat_mat e s (Mat an ac) (Mat bn bc) = do
  inc_inters e
  wnf_enter e s (And (Eql an bn) (Eql ac bc))

wnf_eql_nam_nam :: WnfEql
wnf_eql_nam_nam e s (Nam x) (Nam y) = do
  inc_inters e
  if x == y then
    wnf e s Tru
  else
    wnf e s Fal

wnf_eql_dry_dry :: WnfEql
wnf_eql_dry_dry e s (Dry af ax) (Dry bf bx) = do
  inc_inters e
  wnf_enter e s (And (Eql af bf) (Eql ax bx))

wnf_eql_default :: WnfEql
wnf_eql_default e s a b = do
  wnf e s Fal

-- WNF: Deref Interactions
-- -----------------------

wnf_appg :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appg e s f g a = case g of
  Era    -> wnf_appg_era e s f g a
  Sup {} -> wnf_appg_sup e s f g a
  Lam {} -> wnf_appg_lam e s f g a
  Swi {} -> wnf_enter e (FAppGF (Tup f g) : s) a
  Get {} -> wnf_enter e (FAppGF (Tup f g) : s) a
  Efq    -> wnf_enter e (FAppGF (Tup f g) : s) a
  Use {} -> wnf_enter e (FAppGF (Tup f g) : s) a
  If {}  -> wnf_enter e (FAppGF (Tup f g) : s) a
  Mat {} -> wnf_enter e (FAppGF (Tup f g) : s) a
  _      -> wnf_unwind e s (App (Tup f g) a)

wnf_appg_era :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appg_era e s f Era a = do
  inc_inters e
  wnf e s Era

wnf_appg_sup :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appg_sup e s f (Sup l x y) a = do
  inc_inters e
  (f0,f1) <- clone e l f
  (a0,a1) <- clone e l a
  let app0 = (App (Gua f0 x) a0)
  let app1 = (App (Gua f1 y) a1)
  wnf_enter e s (Sup l app0 app1)

wnf_appg_lam :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appg_lam e s f (Lam x g) a = do
  inc_inters e
  subst VAR e x a
  wnf_enter e s (Gua (App f (Var x)) g)

-- WNF: Gua Pat Interactions (Match reduced argument through guard)
-- ----------------------------------------------------------------

wnf_appgf :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf e s f m a = case m of
  Swi {} -> wnf_appgf_swi e s f m a
  Get {} -> wnf_appgf_get e s f m a
  Efq    -> wnf_appgf_efq e s f m a
  Use {} -> wnf_appgf_use e s f m a
  If {}  -> wnf_appgf_if  e s f m a
  Mat {} -> wnf_appgf_mat e s f m a
  _      -> wnf_unwind e s (App (Gua f m) a)

wnf_appgf_swi :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_swi e s f (Swi z sc) a = case a of
  Era    -> wnf_appgf_swi_era e s f z sc a
  Sup {} -> wnf_appgf_swi_sup e s f z sc a
  Zer    -> wnf_appgf_swi_zer e s f z sc a
  Suc {} -> wnf_appgf_swi_suc e s f z sc a
  _      -> wnf_unwind e s (App f a)

type WnfGuaSwi = Env -> Stack -> Term -> Term -> Term -> Term -> IO Term

wnf_appgf_swi_era :: WnfGuaSwi
wnf_appgf_swi_era e s f z sc Era = do
  wnf_enter e s Era

wnf_appgf_swi_sup :: WnfGuaSwi
wnf_appgf_swi_sup e s f z sc (Sup l a b) = do
  inc_inters e
  (f0,f1) <- clone e l f
  (z0,z1) <- clone e l z
  (s0,s1) <- clone e l sc
  let app0 = App (Gua f0 (Swi z0 s0)) a
  let app1 = App (Gua f1 (Swi z1 s1)) b
  wnf_enter e s (Sup l app0 app1)

wnf_appgf_swi_zer :: WnfGuaSwi
wnf_appgf_swi_zer e s f z sc Zer = do
  inc_inters e
  wnf_enter e s (Gua (App f Zer) z)

wnf_appgf_swi_suc :: WnfGuaSwi
wnf_appgf_swi_suc e s f z sc (Suc n) = do
  inc_inters e
  p <- fresh e
  let fn = (Lam p (App f (Suc (Var p))))
  wnf_enter e s (App (Gua fn sc) n)

wnf_appgf_get :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_get e s f (Get c) a = case a of
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
  _ -> wnf_unwind e s (App (Gua f (Get c)) a)

wnf_appgf_efq :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_efq e s f Efq a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    wnf_enter e s (Sup l (App (Gua f0 Efq) x) (App (Gua f1 Efq) y))
  _ -> wnf_unwind e s (App (Gua f Efq) a)

wnf_appgf_use :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_use e s f (Use u) a = case a of
  Era -> do { inc_inters e; wnf e s Era }
  Sup l x y -> do
    inc_inters e
    (f0, f1) <- clone e l f
    (u0, u1) <- clone e l u
    wnf_enter e s (Sup l (App (Gua f0 (Use u0)) x) (App (Gua f1 (Use u1)) y))
  One -> do
    inc_inters e
    wnf_enter e s (Gua (App f One) u)
  _ -> wnf_unwind e s (App (Gua f (Use u)) a)

wnf_appgf_if :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_if e s f (If ft ff) a = case a of
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
  _ -> wnf_unwind e s (App (Gua f (If ft ff)) a)

wnf_appgf_mat :: Env -> Stack -> Term -> Term -> Term -> IO Term
wnf_appgf_mat e s f (Mat n c) a = case a of
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
  _ -> wnf_unwind e s (App (Gua f (Mat n c)) a)

-- Allocation
-- ==========

-- Allocates a closed term, replacing all bound names with fresh ones.
alloc :: Env -> Term -> IO Term
alloc e term = go IM.empty term where
  go :: IM.IntMap Name -> Term -> IO Term
  go m (Var k)       = return $ Var (IM.findWithDefault k k m)
  go m (Dp0 k)       = return $ Dp0 (IM.findWithDefault k k m)
  go m (Dp1 k)       = return $ Dp1 (IM.findWithDefault k k m)
  go _ Era           = return Era
  go m (Sup l a b)   = Sup l <$> go m a <*> go m b
  go _ Set           = return Set
  go m (All a b)     = All <$> go m a <*> go m b
  go m (App f x)     = App <$> go m f <*> go m x
  go _ Nat           = return Nat
  go _ Zer           = return Zer
  go m (Suc n)       = Suc <$> go m n
  go m (Swi z s)     = Swi <$> go m z <*> go m s
  go m (And a b)     = And <$> go m a <*> go m b
  go m (Eql a b)     = Eql <$> go m a <*> go m b
  go _ (Ref k)       = return $ Ref k
  go _ (Nam k)       = return $ Nam k
  go m (Dry f x)     = Dry <$> go m f <*> go m x
  go m (Gua f g)     = Gua <$> go m f <*> go m g
  go m (Sig a b)     = Sig <$> go m a <*> go m b
  go m (Tup a b)     = Tup <$> go m a <*> go m b
  go m (Get c)       = Get <$> go m c
  go _ Emp           = return Emp
  go _ Efq           = return Efq
  go _ Uni           = return Uni
  go _ One           = return One
  go m (Use u)       = Use <$> go m u
  go _ Bol           = return Bol
  go _ Fal           = return Fal
  go _ Tru           = return Tru
  go m (If f t)      = If <$> go m f <*> go m t
  go m (Lst t)       = Lst <$> go m t
  go _ Nil           = return Nil
  go m (Con h t)     = Con <$> go m h <*> go m t
  go m (Mat n c)     = Mat <$> go m n <*> go m c
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

snf :: Env -> Int -> Term -> IO Term
snf e d x = do
  !x' <- wnf e [] x
  case x' of
    Var k -> do
      return $ Var k
    Dp0 k -> do
      return $ Dp0 k
    Dp1 k -> do
      return $ Dp1 k
    Era -> do
      return Era
    Sup l a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Sup l a' b'
    Dup k l v t -> do
      subst DP0 e k (Nam (int_to_name d ++ "₀"))
      subst DP1 e k (Nam (int_to_name d ++ "₁"))
      v' <- snf e d v
      t' <- snf e d t
      return $ Dup d l v' t'
    Set -> do
      return Set
    All a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ All a' b'
    Lam k f -> do
      subst VAR e k (Nam (int_to_name d))
      f' <- snf e (d + 1) f
      return $ Lam d f'
    App f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ App f' x'
    Nat -> do
      return Nat
    Zer -> do
      return Zer
    Suc p -> do
      p' <- snf e d p
      return $ Suc p'
    Swi z s -> do
      z' <- snf e d z
      s' <- snf e d s
      return $ Swi z' s'
    And a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ And a' b'
    Eql a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Eql a' b'
    Ref k -> do
      return $ Ref k
    Nam k -> do
      return $ Nam k
    Dry f x -> do
      f' <- snf e d f
      x' <- snf e d x
      return $ Dry f' x'
    Gua f g -> do
      g' <- snf e d g
      return g'
    Sig a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Sig a' b'
    Tup a b -> do
      a' <- snf e d a
      b' <- snf e d b
      return $ Tup a' b'
    Get c -> do
      c' <- snf e d c
      return $ Get c'
    Emp -> do
      return Emp
    Efq -> do
      return Efq
    Uni -> do
      return Uni
    One -> do
      return One
    Use u -> do
      u' <- snf e d u
      return $ Use u'
    Bol -> do
      return Bol
    Fal -> do
      return Fal
    Tru -> do
      return Tru
    If f t -> do
      f' <- snf e d f
      t' <- snf e d t
      return $ If f' t'
    Lst t -> do
      t' <- snf e d t
      return $ Lst t'
    Nil -> do
      return Nil
    Con h t -> do
      h' <- snf e d h
      t' <- snf e d t
      return $ Con h' t'
    Mat n c -> do
      n' <- snf e d n
      c' <- snf e d c
      return $ Mat n' c'

-- Collapsing
-- ==========

collapse :: Env -> Term -> IO Term
collapse e x = do
  !x <- wnf e [] x
  case x of
    Era -> do
      return Era
    (Sup l a b) -> do
      a' <- collapse e a
      b' <- collapse e b
      return $ Sup l a' b'
    Set -> do
      return Set
    All a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inj e (Lam aV (Lam bV (All (Var aV) (Var bV)))) [a',b']
    (Lam k f) -> do
      fV <- fresh e
      f' <- collapse e f
      inj e (Lam fV (Lam k (Var fV))) [f']
    (App f x) -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inj e (Lam fV (Lam xV (App (Var fV) (Var xV)))) [f',x']
    Nat -> do
      return Nat
    Zer -> do
      return Zer
    (Suc p) -> do
      pV <- fresh e
      p' <- collapse e p
      inj e (Lam pV (Suc (Var pV))) [p']
    (Swi z s) -> do
      zV <- fresh e
      sV <- fresh e
      z' <- collapse e z
      s' <- collapse e s
      inj e (Lam zV (Lam sV (Swi (Var zV) (Var sV)))) [z',s']
    (And a b) -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inj e (Lam aV (Lam bV (And (Var aV) (Var bV)))) [a',b']
    (Eql a b) -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inj e (Lam aV (Lam bV (Eql (Var aV) (Var bV)))) [a',b']
    Nam n -> do
      return $ Nam n
    Dry f x -> do
      fV <- fresh e
      xV <- fresh e
      f' <- collapse e f
      x' <- collapse e x
      inj e (Lam fV (Lam xV (Dry (Var fV) (Var xV)))) [f',x']
    (Gua f g) -> do
      collapse e g
    Sig a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inj e (Lam aV (Lam bV (Sig (Var aV) (Var bV)))) [a',b']
    Tup a b -> do
      aV <- fresh e
      bV <- fresh e
      a' <- collapse e a
      b' <- collapse e b
      inj e (Lam aV (Lam bV (Tup (Var aV) (Var bV)))) [a',b']
    Get c -> do
      cV <- fresh e
      c' <- collapse e c
      inj e (Lam cV (Get (Var cV))) [c']
    Emp -> do
      return Emp
    Efq -> do
      return Efq
    Uni -> do
      return Uni
    One -> do
      return One
    Use u -> do
      uV <- fresh e
      u' <- collapse e u
      inj e (Lam uV (Use (Var uV))) [u']
    Bol -> do
      return Bol
    Fal -> do
      return Fal
    Tru -> do
      return Tru
    If f t -> do
      fV <- fresh e
      tV <- fresh e
      f' <- collapse e f
      t' <- collapse e t
      inj e (Lam fV (Lam tV (If (Var fV) (Var tV)))) [f',t']
    Lst t -> do
      tV <- fresh e
      t' <- collapse e t
      inj e (Lam tV (Lst (Var tV))) [t']
    Nil -> do
      return Nil
    Con h t -> do
      hV <- fresh e
      tV <- fresh e
      h' <- collapse e h
      t' <- collapse e t
      inj e (Lam hV (Lam tV (Con (Var hV) (Var tV)))) [h',t']
    Mat n c -> do
      nV <- fresh e
      cV <- fresh e
      n' <- collapse e n
      c' <- collapse e c
      inj e (Lam nV (Lam cV (Mat (Var nV) (Var cV)))) [n',c']
    x -> do
      return $ x

inj :: Env -> Term -> [Term] -> IO Term
inj e f (x : xs) = do
  !x' <- wnf e [] x
  case x' of
    (Sup l a b) -> do
      (f0  , f1 ) <- clone e l f
      (xs0 , xs1) <- clone_list e l xs
      a' <- inj e f0 (a : xs0)
      b' <- inj e f1 (b : xs1)
      return $ Sup l a' b'
    x' -> do
      inj e (App f x') xs
inj e f [] = do
  return $ f

-- Flattening
-- ==========

flatten :: Term -> [Term]
flatten term = bfs [term] [] where
  bfs []     acc = reverse acc
  bfs (t:ts) acc = case t of
    Sup _ a b -> bfs (ts ++ [a, b]) acc
    _         -> bfs ts (t : acc)

-- Main
-- ====

f :: Int -> String
f n = "λf." ++ dups ++ final where
  dups  = concat [dup i | i <- [0..n-1]]
  dup 0 = "!F00&A=f;"
  dup i = "!F" ++ pad i ++ "&A=λx" ++ pad (i-1) ++ ".(F" ++ pad (i-1) ++ "₀ (F" ++ pad (i-1) ++ "₁ x" ++ pad (i-1) ++ "));"
  final = "λx" ++ pad (n-1) ++ ".(F" ++ pad (n-1) ++ "₀ (F" ++ pad (n-1) ++ "₁ x" ++ pad (n-1) ++ "))"
  pad x = if x < 10 then "0" ++ show x else show x

book :: String
book = unlines
  [ "@id  = λa.a"
  , "@not = λ{0:1+0;1+:λp.0}"
  , "@dbl = λ{0:0;1+:λp.1+1+(@dbl p)}"
  , "@and = λ{0:λ{0:0;1+:λp.0};1+:λp.λ{0:0;1+:λp.1+0}}"
  , "@add = λ{0:λb.b;1+:λa.λb.1+(@add a b)}"
  , "@sum = λ{0:0;1+:λp.!P&S=p;1+(@add P₀ (@sum P₁))}"
  , "@foo = &L{λx.x,λ{0:0;1+:λp.p}}"
  , "@gen = !F&A=@gen &A{λx.!X&B=x;&B{X₀,1+X₁},λ{0:&C{0,1};1+:λp.!G&D=F₁;!P&D=p;&D{(G₀ P₀),!H&E=G₁;!Q&E=P₁;1+&E{(H₀ Q₀),1+(H₁ Q₁)}}}}"
  ]

tests :: [(String,String)]
tests =
  [ ("(@not 0)", "1")
  , ("(@not 1+0)", "0")
  , ("!F&L=@id;!G&L=F₀;λx.(G₁ x)", "λa.a")
  , ("(@and 0 0)", "0")
  , ("(@and &L{0,1+0} 1+0)", "&L{0,1}")
  , ("(@and &L{1+0,0} 1+0)", "&L{1,0}")
  , ("(@and 1+0 &L{0,1+0})", "&L{0,1}")
  , ("(@and 1+0 &L{1+0,0})", "&L{1,0}")
  , ("λx.(@and 0 x)", "λa.(@and 0 a)")
  , ("λx.(@and x 0)", "λa.(@and a 0)")
  , ("(@sum 1+1+1+0)", "6")
  , ("λx.(@sum 1+1+1+x)", "λa.3+(@add a 2+(@add a 1+(@add a (@sum a))))")
  , ("(@foo 0)", "&L{0,0}")
  , ("(@foo 1+1+1+0)", "&L{3,2}")
  , ("λx.(@dbl 1+1+x)", "λa.4+(@dbl a)")
  , ("("++f 2++" λX.(X λT0.λF0.F0 λT1.λF1.T1) λT2.λF2.T2)", "λa.λb.a")
  , ("1+&L{0,1}", "&L{1,2}")
  , ("1+&A{&B{0,1},&C{2,3}}", "&A{&B{1,2},&C{3,4}}")
  , ("λa.!A&L=a;&L{A₀,A₁}", "&L{λa.a,λa.a}")
  , ("λa.λb.!A&L=a;!B&L=b;&L{λx.(x A₀ B₀),λx.(x A₁ B₁)}", "&L{λa.λb.λc.(c a b),λa.λb.λc.(c a b)}")
  , ("λt.(t &A{1,2} 3)", "&A{λa.(a 1 3),λa.(a 2 3)}")
  , ("λt.(t 1 &B{3,4})", "&B{λa.(a 1 3),λa.(a 1 4)}")
  , ("λt.(t &A{1,2} &A{3,4})", "&A{λa.(a 1 3),λa.(a 2 4)}")
  , ("λt.(t &A{1,2} &B{3,4})", "&A{&B{λa.(a 1 3),λa.(a 1 4)},&B{λa.(a 2 3),λa.(a 2 4)}}")
  , ("@gen", "&A{&B{λa.a,λa.1+a},&C{&D{λ{0:0;1+:λa.(@gen a)},&E{λ{0:0;1+:λa.1+(@gen a)},λ{0:0;1+:λa.2+(@gen a)}}},&D{λ{0:1;1+:λa.(@gen a)},&E{λ{0:1;1+:λa.1+(@gen a)},λ{0:1;1+:λa.2+(@gen a)}}}}}")
  , ("λx.(@gen 2+x)", "&A{&B{λa.2+a,λa.3+a},&D{λa.(@gen a),&E{λa.2+(@gen a),λa.4+(@gen a)}}}")
  , ("(@gen 2)", "&A{&B{2,3},&D{&C{0,1},&E{&C{2,3},&C{4,5}}}}")
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
  ]

run :: String -> String -> IO ()
run book_src term_src = do
  !env <- new_env $ read_book book_src
  !ini <- getCPUTime
  !val <- alloc env $ read_term term_src
  !val <- collapse env val
  !val <- snf env 1 val
  !end <- getCPUTime
  !itr <- readIORef (env_inters env)
  !dt  <- return $ fromIntegral (end - ini) / (10^12)
  !ips <- return $ fromIntegral itr / dt
  putStrLn $ show val
  putStrLn $ "- Itrs: " ++ show itr ++ " interactions"
  printf "- Time: %.3f seconds\n" (dt :: Double)
  printf "- Perf: %.2f M interactions/s\n" (ips / 1000000 :: Double)

test :: IO ()
test = forM_ tests $ \ (src, exp) -> do
  env <- new_env $ read_book book
  det <- collapse env $ read_term src
  det <- show <$> snf env 1 det
  if det == exp then do
    putStrLn $ "[PASS] " ++ src ++ " → " ++ det
  else do
    putStrLn $ "[FAIL] " ++ src
    putStrLn $ "  - expected: " ++ exp
    putStrLn $ "  - detected: " ++ det

main :: IO ()
main = test
