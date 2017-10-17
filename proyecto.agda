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
  neg   : Expr n nat → Expr n nat
  plus  : Expr n nat → Expr n nat -> Expr n nat
  minus : Expr n nat → Expr n nat -> Expr n nat
  times : Expr n nat → Expr n nat -> Expr n nat
  div   : Expr n nat → Expr n nat -> Expr n nat
  true  : Expr n bool
  false : Expr n bool
  not   : Expr n bool → Expr n bool
  and   : Expr n bool → Expr n bool → Expr n bool
  or    : Expr n bool → Expr n bool → Expr n bool
  Eq    : Expr n bool → Expr n bool → Expr n bool
  Neq   : Expr n bool → Expr n bool → Expr n bool
  Lt    : Expr n bool → Expr n bool → Expr n bool



  


{-data IntExpr : Set where
  const : ℕ → IntExpr
  Neg   : IntExpr → IntExpr
-}  
