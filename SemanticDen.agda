module SemanticDen where

open import Data.Nat
open import DataType
open import Data.Bool

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

[_]' : Type → Set
[ nat ]'     = ℕ
[ bool ]'    = Bool
[ command ]' = Omega

star : (f :  State -> Omega) -> Omega -> Omega
star f (Term st)  = f st
star f (Abort st) = Abort st
star f (Out n w)  = Out n (star f w)
star f (In v g)   = In v (\ n -> star f (g n))

dagger : (f :  State -> State) -> Omega -> Omega
dagger f (Term st)  = Term (f st)
dagger f (Abort st) = Abort (f st)
dagger f (Out n w)  = Out n (dagger f w)
dagger f (In v w)   = In v (\ n -> dagger f (w n))

mas : (f : State -> Omega) -> Omega -> Omega
mas f (Term st)  = Term st
mas f (Abort st) = f st
mas f (Out n w)    = Out n (mas f w)
mas f (In v g)     = In v (\ n -> mas f (g n))

[[_]] : ∀ {t} -> Expr t → (st : State) → [ t ]'
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
[[ Assign v e ]] st  = Term (set st v ([[ e ]] st))
[[ If b c1 c2 ]] st with [[ b ]] st
... | true  = [[ c1 ]] st
... | false = [[ c2 ]] st
[[ Seq c1 c2 ]] st    = star [[ c2 ]] ([[ c1 ]] st)
[[ Newvar v e c ]] st = dagger (\ st' -> set st' v (get v st)) ([[ c ]] (set st v ([[ e ]] st))) 
[[ Dame v ]] st       = In v (\ n -> Term (set st v n))
[[ Toma v ]] st         = Out ([[ v ]] st) (Term st)
[[ Agarrame c1 c2 ]] st = mas [[ c2 ]] ( [[ c1 ]] st )
