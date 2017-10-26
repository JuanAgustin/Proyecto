import Data.Bool as Bool using (not)
open import Data.Nat
open import Data.Bool hiding (not)
open import Data.Vec
open import Data.List
open import Data.String

data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < x , y > = x

snd : {A B : Set} → A × B → B
snd < x , y > = y

data Type : Set where
  bool : Type
  nat : Type

State : Set
State = List (< Costring , ℕ >)




data Expr : Type → Set where
  const :  Expr nat
  var   :  Expr nat
{-  neg   : Expr n nat → Expr n nat -}
  plus  : Expr nat → Expr nat -> Expr nat
  minus : Expr nat → Expr nat -> Expr nat
  times : Expr nat → Expr nat -> Expr nat
{-  div   : Expr n nat → Expr n nat -> Expr n nat -}
  true  : Expr bool
  false : Expr bool
  op_not   : Expr bool → Expr bool
  op_and   : Expr bool → Expr bool → Expr bool
  op_or    : Expr bool → Expr bool → Expr bool
  op_Eq    : Expr bool → Expr bool → Expr bool
{-  Neq   : Expr n bool → Expr n bool → Expr n bool -}
  Lt    : Expr bool → Expr bool → Expr bool

{-
[_]' : Type → Set
[ nat ]'  = ℕ
[ bool ]' = Bool

[[_]] : ∀ {n t} → Expr n t → State n → [ t ]'
[[ const x ]] st   = x
{- [[ neg a ]] st     = - [[ a ]] st -}
[[ plus a b ]] st  = [[ a ]] st + [[ b ]] st
[[ minus a b ]] st = [[ a ]] st ∸ [[ b ]] st
[[ times a b ]] st = [[ a ]] st * [[ b ]] st
{- [[ div a b ]] st   = [[ a ]] st / [[ b ]] st -}
[[ true ]] st      = true
[[ false ]] st     = false
[[ not a ]] st     = Bool.not ([[ a ]] st)
[[ and a b ]] st   = [[ a ]] st ∧ [[ b ]] st
[[ or a b ]] st    = [[ a ]] st ∨ [[ b ]] st
{- [[ Neq a b ]] st   = [[ a ]] st ‌≠ [[ b ]] st -}
[[ Lt a b ]] st    = [[ a ]] s


  -}


{-data IntExpr : Set where
  const : ℕ → IntExpr
  Neg   : IntExpr → IntExpr
-}  
