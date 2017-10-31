{-import Data.Bool as Bool using (not)-}
open import Data.Nat
open import Data.Bool {-hiding (not)-}
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

_eq_ : ℕ -> ℕ -> Bool
zero  eq zero  = true
zero  eq suc n = false
suc n eq zero  = false
suc n eq suc m = n eq m

_neq_ : ℕ -> ℕ -> Bool
zero  neq zero  = false
zero  neq suc n = true
suc n neq zero  = true
suc n neq suc m = n neq m

_lt_ : ℕ -> ℕ -> Bool
zero  lt zero  = false
zero  lt suc n = true
suc n lt zero  = false
suc n lt suc m = n lt m

data State : List ℕ -> Set where
  ε        : State []
  _⟼_,_   : forall {ls} ->
            String -> (n : ℕ) -> State ls -> State (n :: ls)

_∈_ : forall {ls} -> String -> State ls -> Bool
s ∈ ε      = false
s ∈ (s' ⟼ _ , st) with s == s'
...            | true  = true
...            | false = s ∈ st

{-get : {ls : List ℕ}(s : String)(st : State ls) -> (p : IsTrue (s ∈ st)) -> ℕ
get s ε ()
get s (s' ⟼ n , st) p with s == s'
... | true  = n
... | false = get s st p-}


{- Si la variable no se encuentra en el estado, devuelvo 'cero' -}
get : {ls : List ℕ}(s : String)(st : State ls) -> ℕ
get s ε = 0
get s (s' ⟼ n , st) with s == s'
... | true  = n
... | false = get s st
 

{-set : {ls : List ℕ}{ls' : List ℕ}(st : State ls)(s : String)(n : ℕ) -> State ls'
set ε s n = s ⟼ n , ε
set (s' ⟼ n' , st) s n with s == s'
... | true  = s ⟼ n , st
... | false = s' ⟼ n' , set st s n-}



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
  op_not   : Expr bool → Expr bool
  op_and   : Expr bool → Expr bool → Expr bool
  op_or    : Expr bool → Expr bool → Expr bool
  op_Eq    : Expr nat → Expr nat → Expr bool
  op_Neq   : Expr nat → Expr nat → Expr bool
  Lt       : Expr nat → Expr nat → Expr bool






[_]' : Type → Set
[ nat ]'  = ℕ
[ bool ]' = Bool



[[_]] : ∀ {t} {ls : List ℕ} → Expr t → (st : State ls) → [ t ]'
[[ const x ]] st     = x
[[ var s ]] st       = get s st
{-[[ neg a ]] st     = - [[ a ]] st-}
[[ plus a b ]] st    = [[ a ]] st + [[ b ]] st
[[ minus a b ]] st   = [[ a ]] st ∸ [[ b ]] st
[[ times a b ]] st   = [[ a ]] st * [[ b ]] st
{-[[ div a b ]] st   = [[ a ]] st / [[ b ]] st-}
[[ true ]] st        = true
[[ false ]] st       = false
[[ op_not a ]] st    = not ([[ a ]] st)
[[ op_and a b ]] st  = [[ a ]] st ∧ [[ b ]] st
[[ op_or a b ]] st   = [[ a ]] st ∨ [[ b ]] st
[[ op_Eq a b ]] st   = [[ a ]] st eq [[ b ]] st
[[ op_Neq a b ]] st  =  [[ a ]] st neq [[ b ]] st
[[ Lt a b ]] st      = [[ a ]] st lt [[ b ]] st


  




