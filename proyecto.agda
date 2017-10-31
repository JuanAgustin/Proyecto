{-import Data.Bool as Bool using (not)-}
open import Data.Nat
open import Data.Bool {-hiding (not)-}
open import Data.String
open import Function using (_∘_; _$_)


data List (A : Set) : Set where
  []    : List A
  _::_  : A -> List A -> List A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data IsTrue : Bool -> Set where
  isTrue : IsTrue true




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





data Type : Set where
  bool : Type
  nat : Type
  command : Type

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
 {- Assign   : String -> Expr nat -> Expr command-}
  If       : Expr bool -> Expr command -> Expr command -> Expr command
  Seq      : Expr command -> Expr command -> Expr command
{- Newvar  : String -> Expr nat -> Expr command -}
{- Dame    : String -> Expr command-}
  Toma     : Expr nat -> Expr command
  Agarrame : Expr command -> Expr command -> Expr command


data Omega : Set where
  Term  : {ls : List ℕ} -> (State ls) -> Omega
  Abort : {ls : List ℕ} -> (State ls) -> Omega
  Out   : ℕ -> Omega -> Omega
  In    : String -> (ℕ -> Omega) -> Omega
  

[_]' : Type → Set
[ nat ]'     = ℕ
[ bool ]'    = Bool
[ command ]' = Omega

star : (f : {ls : List ℕ} -> State ls -> Omega) -> Omega -> Omega
star f (Term st)  = f st
star f (Abort st) = Abort st
star f (Out n w)  = Out n (star f w)
star f (In v g)   = In v (\ n -> star f (g n))

dagger : (f : {ls : List ℕ} -> State ls -> State ls) -> Omega -> Omega
dagger f (Term st)  = Term (f st)
dagger f (Abort st) = Abort (f st)
dagger f (Out n w)  = Out n (dagger f w)
dagger f (In v w)   = In v (\ n -> dagger f (w n))

mas : (f : {ls : List ℕ} -> State ls -> Omega) -> Omega -> Omega
mas f (Term st)  = Term st
mas f (Abort st) = f st
mas f (Out n w)    = Out n (mas f w)
mas f (In v g)     = In v (\ n -> mas f (g n))

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
[[ opNot a ]] st     = not ([[ a ]] st)
[[ opAnd a b ]] st   = [[ a ]] st ∧ [[ b ]] st
[[ opOr a b ]] st    = [[ a ]] st ∨ [[ b ]] st
[[ opEq a b ]] st    = [[ a ]] st eq [[ b ]] st
[[ opNeq a b ]] st   =  [[ a ]] st neq [[ b ]] st
[[ Lt a b ]] st      = [[ a ]] st lt [[ b ]] st
[[ Skip ]] st        = Term st
[[ Morite ]] st      = Abort st
{- [[ Assign v e ]] st  = Me falta el set! -}
[[ If b c1 c2 ]] st with [[ b ]] st
... | true  = [[ c1 ]] st
... | false = [[ c2 ]] st
[[ Seq c1 c2 ]] st    = star [[ c2 ]] ([[ c1 ]] st)
{-[[ Newvar v e c ]] st = dagger (\ st' -> set st' v (get st v)) ([[ c ]] (set st v ([[ e ]] st))) -}
{-[[ Dame v ]] st       = In v (\ n -> Term (set st v n)) -}
[[ Toma v ]] st         = Out ([[ v ]] st) (Term st)
[[ Agarrame c1 c2 ]] st = mas [[ c2 ]] ( [[ c1 ]] st )

