import Data.Bool as Bool using (not)
open import Data.Nat
open import Data.Bool hiding (not)
open import Data.String

data List (A : Set) : Set where
  []    : List A
  _::_  : A -> List A -> List A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data IsTrue : Bool -> Set where
  isTrue : IsTrue true


data Type : Set where
  bool : Type
  nat : Type

{-State : Set
State = List (String × ℕ)-}

data State : List ℕ -> Set where
  ε        : State []
  _⟼_,_   : forall {s ls} ->
            String -> (n : ℕ) -> State ls -> State (n :: ls)

_∈_ : forall {ls} -> String -> State ls -> Bool
s ∈ ε      = false
s ∈ (s' ⟼ _ , st) with s == s'
...            | true  = true
...            | false = s ∈ st

get : {ls : List ℕ}(s : String)(st : State ls) -> (p : IsTrue (s ∈ st)) -> ℕ
get s ε ()
get s (s' ⟼ n , st) p with s == s'
... | true  = n
... | false = get s st p



data Expr : Type → Set where
  const : ℕ →  Expr nat
  var   : String → Expr nat
 {- neg   : Expr nat → Expr nat-}
  plus  : Expr nat → Expr nat -> Expr nat
  minus : Expr nat → Expr nat -> Expr nat
  times : Expr nat → Expr nat -> Expr nat
  div   : Expr nat → Expr nat -> Expr nat
  {-true  : Expr bool
  false : Expr bool
  op_not   : Expr bool → Expr bool
  op_and   : Expr bool → Expr bool → Expr bool
  op_or    : Expr bool → Expr bool → Expr bool
  op_Eq    : Expr bool → Expr bool → Expr bool
  Neq   : Expr bool → Expr bool → Expr bool
  Lt    : Expr bool → Expr bool → Expr bool-}

  


[_]' : Type → Set
[ nat ]'  = ℕ
[ bool ]' = Bool



[[_]] : ∀ {t} {ls : List ℕ} → Expr t → (st : State ls) → [ t ]'
[[ const x ]] st   = x
{-[[ var s ]] st     = get s st-}
{- [[ neg a ]] st     = - [[ a ]] st -}
[[ plus a b ]] st  = [[ a ]] st + [[ b ]] st
[[ minus a b ]] st = [[ a ]] st ∸ [[ b ]] st
[[ times a b ]] st = [[ a ]] st * [[ b ]] st
{- [[ div a b ]] st   = [[ a ]] st / [[ b ]] st -}
{-[[ true ]] st      = true
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
