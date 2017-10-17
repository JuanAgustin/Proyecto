import Data.Bool as Bool using (not)
open import Data.Nat
open import Data.Bool hiding (not)
open import Data.Vec

data Type : Set where
  bool : Type
  nat : Type

State : ℕ → Set
State = Vec ℕ


data Expr (n : ℕ) : Type → Set where
  const : ℕ → Expr n nat
  var   : ℕ → Expr n nat
{-  neg   : Expr n nat → Expr n nat -}
  plus  : Expr n nat → Expr n nat -> Expr n nat
  minus : Expr n nat → Expr n nat -> Expr n nat
  times : Expr n nat → Expr n nat -> Expr n nat
{-  div   : Expr n nat → Expr n nat -> Expr n nat -}
  true  : Expr n bool
  false : Expr n bool
  not   : Expr n bool → Expr n bool
  and   : Expr n bool → Expr n bool → Expr n bool
  or    : Expr n bool → Expr n bool → Expr n bool
  Eq    : Expr n bool → Expr n bool → Expr n bool
{-  Neq   : Expr n bool → Expr n bool → Expr n bool -}
  Lt    : Expr n bool → Expr n bool → Expr n bool


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
[[ Eq a b ]] st    = [[ a ]] st ≟ [[ b ]] st
{- [[ Neq a b ]] st   = [[ a ]] st ‌≠ [[ b ]] st -}
[[ Lt a b ]] st    = [[ a ]] s


  


{-data IntExpr : Set where
  const : ℕ → IntExpr
  Neg   : IntExpr → IntExpr
-}  
