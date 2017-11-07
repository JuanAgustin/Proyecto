module DataType where

open import Data.Nat
open import Data.String
open import Data.Bool

data List (A : Set) : Set where
  []    : List A
  _::_  : A -> List A -> List A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Type : Set where
  bool : Type
  nat : Type
  command : Type

data State : Set where
  ε        : State
  _⟼_,_   : String -> (n : ℕ) -> State -> State

get : (s : String)(st : State) -> ℕ
get s ε = 0
get s (s' ⟼ n , st) with s == s'
... | true  = n
... | false = get s st
 

set : (st : State)(s : String)(n : ℕ) -> State
set ε s n = s ⟼ n , ε
set (s' ⟼ n' , st) s n with s == s'
... | true  = s ⟼ n , st
... | false = s' ⟼ n' , set st s n

data Expr : Type → Set where
  const    : ℕ →  Expr nat
  var      : String → Expr nat
 {- neg    : Expr nat → Expr nat -}
  plus     : Expr nat → Expr nat -> Expr nat
  minus    : Expr nat → Expr nat -> Expr nat
  times    : Expr nat → Expr nat -> Expr nat
  {-div    : Expr nat → Expr nat -> Expr nat-}
  true     : Expr bool
  false    : Expr bool
  opNot   : Expr bool → Expr bool
  opAnd   : Expr bool → Expr bool → Expr bool
  opOr    : Expr bool → Expr bool → Expr bool
  opEq    : Expr nat → Expr nat → Expr bool
  opNeq   : Expr nat → Expr nat → Expr bool
  Lt       : Expr nat → Expr nat → Expr bool
  Skip     : Expr command
  Morite   : Expr command
  Assign   : String -> Expr nat -> Expr command
  If       : Expr bool -> Expr command -> Expr command -> Expr command
  Seq      : Expr command -> Expr command -> Expr command
  Newvar  : String -> Expr nat -> Expr command -> Expr command
  Dame    : String -> Expr command
  Toma     : Expr nat -> Expr command
  Agarrame : Expr command -> Expr command -> Expr command


data Omega : Set where
  Term  :  (State) -> Omega
  Abort :  (State) -> Omega
  Out   : ℕ -> Omega -> Omega
  In    : String -> (ℕ -> Omega) -> Omega
