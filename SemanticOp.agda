module SemanticOp where

open import DataType
open import Data.Nat
open import Data.String
open import SemanticDen
open import Data.Bool
open import Data.Sum
open import Relation.Binary.Core


data _even : ℕ → Set where
  ZERO : zero even
  STEP : (x : ℕ) → x even → suc (suc x) even

cuatro = suc (suc (suc (suc zero)))

proof₁ : cuatro even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)






{- DEFINÍ TOD0 EN UNA SOLA RELACIÓN -}

data _⇝_ : (Expr command × State) -> (Expr command × State) ⊎ Omega -> Set where
  Skip : (st : State) -> < Skip , st > ⇝ (inj₂ (Term st))
  Assign : (v : String) (e : Expr nat) (st : State) ->
         < (Assign v e) , st > ⇝ (inj₂ (Term (set st v ([[ e ]] st))))
  Seq1 : {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₂ (Term st₁)) ->
         < Seq c₀ c₁ , st₀ > ⇝ (inj₁ < c₁ , st₁ >)
  Seq2 : {c₀ c₀' c₁ : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₁ < c₀' , st₁ >) ->
         < Seq c₀ c₁ , st₀ > ⇝ (inj₁  < Seq c₀' c₁ , st₁ >)
  Seq3 :  {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) ->
         < (Seq c₀ c₁) , st₀ > ⇝ (inj₂ (Abort st₁))
  IfTrue : {e : Expr bool} {c₀ c₁ : Expr command} {st : State} ->
         [[ e ]] st ≡ true  ->
         < If e c₀ c₁ , st > ⇝ (inj₁ < c₀ , st >) 
  IfFalse : {e : Expr bool} {c₀ c₁ : Expr command} {st : State} ->
          [[ e ]] st ≡ false ->
          < If e c₀ c₁ , st > ⇝ (inj₁ < c₁ , st >)
  NewVar1 : (v : String) (e : Expr nat) {c₀ : Expr command} {st₀ : State} {st₁ : State} ->
          < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₂ (Term st₁)) ->
          < (Newvar v e c₀) , st₀ > ⇝  (inj₂ (Term (set st₁ v (get v st₀))))
  NewVar2 : (v : String) (e : Expr nat) {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
          < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₁ < c₁ , st₁ >) ->
          < (Newvar v e c₀) , st₀ > ⇝ (inj₁ < (Newvar v (const (get v st₁)) c₁) , (set st₁ v (get v st₀)) >)
  NewVar3 : (v : String) (e : Expr nat) {c₀ : Expr command} {st₀ st₁ : State} ->
          < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₂ (Abort st₁)) ->
          < (Newvar v e c₀) , st₀ > ⇝ (inj₂ (Abort (set st₁ v (get v st₀))))
  Fail    : {st : State} ->
          < Fail , st > ⇝ (inj₂ (Abort st))
  Catchin1 : {c₀ : Expr command} {c₁ : Expr command} {st₀ : State} {st₁ : State} ->
           < c₀ , st₀ > ⇝ (inj₂ (Term st₁)) ->
           < (Agarrame c₀ c₁) , st₀ > ⇝ (inj₂ (Term st₁))
  Catchin2 : {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
           < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) ->
           < (Agarrame c₀ c₁) , st₀ > ⇝ (inj₁ < c₁ ,  st₁ >)
  Catchin3 : {c₀ c₁ c₂ : Expr command} {st₀ st₁ : State} ->
           < c₀ , st₀ > ⇝ (inj₁ < c₁ , st₁ >) ->
           < (Agarrame c₀ c₂) , st₀ > ⇝ (inj₁ < (Agarrame c₁ c₂) , st₁ >)


data _⇝*_ : (Expr command × State) ⊎ Omega -> (Expr command × State) ⊎ Omega -> Set where
  Reflex : {y : (Expr command × State) ⊎ Omega} ->
         y ⇝* y
  CBase : {cmd : Expr command} {st : State} {y : (Expr command × State) ⊎ Omega} ->
        < cmd , st > ⇝ y ->
        (inj₁ < cmd , st >) ⇝* y  
  Transit : {y₀ y₁ y₂ : (Expr command × State) ⊎ Omega} ->
       y₀ ⇝* y₁ ->
       y₁ ⇝* y₂ ->
       y₀ ⇝* y₂ 


StateVacio = ε
State₁ =  "x" ⟼ 2 , ε
State₂ =  "y" ⟼ 2 , ("x" ⟼ 2 , ε)


{- Haciendo las pruebas me fui dando cuenta de que argumentos los podía poner como implícitos y fui cambiando-}

{-
proof₂ : < Skip , StateVacio > ⇝ (inj₂ (Term StateVacio))
proof₂ = Skip 

proof₃ : inj₁ < Skip , StateVacio > ⇝* inj₂ (Term StateVacio)
proof₃ = CBase Skip


proof₄ : inj₁ < Assign "x" (const 4) , State₁ >  ⇝* inj₂ (Term ("x" ⟼ 4 , ε))
proof₄ = CBase Assign

proof₅ : inj₁ < Assign "y" (const 10) , State₁ >  ⇝* inj₂ (Term ("x" ⟼ 2 , ("y" ⟼ 10 , StateVacio)))
proof₅ =  CBase Assign

proof_seq₁ : inj₁ < Seq (Assign "x" (const 4)) (Skip) , State₁ >  ⇝* inj₂ (Term ("x" ⟼ 4 , ε))
proof_seq₁ = Transit (CBase (Seq1 Assign)) (CBase Skip)

proof_if₁ : inj₁ < If (opEq (const 4) (const 4)) Skip (Assign "x" (const 4)) , State₁ > ⇝* inj₂ (Term State₁)


proof_if₁ = Transit (CBase (IfTrue refl)) (CBase S

proof_if₂ : inj₁ < If (opEq (const 2) (const 4)) Skip (Assign "x" (const 4)) , State₁ > ⇝* inj₂ (Term ("x" ⟼ 4 , ε))
proof_if₂ = Transit (CBase (IfFalse refl)) (CBase Assign)

-}




{-
correction : {cmd : Expr command} -> {st st' : State} -> < cmd , st > ⇝ inj₂ (Term st') -> [[ cmd ]] st ≡ Term st'
correction Skip = [[ Skip ]] st ≡ Term st'
-}

{-
correction : ∀ (st : State) -> Expr command
correction st = Skip
-}

{-
correction : {cmd : Expr command} -> ∀ {st st' : State} -> < cmd , st > ⇝ inj₂ (Term st') ->  [[ cmd ]] st ≡ Term st'
correction (Skip st) =  refl
correction (Assign v e st) = refl
 = ?
-}

{-
correction : {cmd : Expr command} -> ∀ {st st' : State} -> < cmd , st > ⇝ inj₂ (Term st') ->  [[ cmd ]] st ≡ Term st'
correction (Skip st) = refl
correction (Assign v e st) = refl
correction (Catchin1 .Skip st' (Skip .st')) = refl
correction (Catchin1 .(Assign v e) st (Assign v e .st)) = refl
correction (Catchin1 .(Agarrame c₀ c₂) st₀ (Catchin1 c₀ {c₂} .st₀ prf)) = {!!}
-}

{-
correction : {cmd : Expr command} -> ∀ {st st' : State} -> < cmd , st > ⇝ inj₂ (Term st') ->  [[ cmd ]] st ≡ Term st'
correction (Skip st) = refl
correction (Assign v e st) = refl
correction (Catchin1 st (Skip .st)) = refl
correction (Catchin1 .(set st v ([[ e ]] st)) (Assign v e st)) = {!!}
correction (Catchin1 st' (Catchin1 .st' prf)) = {!!}
-}

open import Relation.Binary.PropositionalEquality
--postulate
masProp₁ : ∀ {f g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡  Term st₁ -> mas g (f st₀) ≡ Term st₁
masProp₁ {g = g} eq = cong (mas g) eq


daggerProp₁ : ∀ {f : State -> Omega} {g : State -> State} {st₀ st₁ : State} -> f st₀ ≡  Term st₁ -> dagger g (f st₀) ≡ Term (g st₁)
daggerProp₁ {g = g} eq = cong (dagger g) eq


daggerProp₂ : ∀ {f : State -> Omega} {g : State -> State} {st₀ st₁ : State} -> f st₀ ≡  Abort st₁ -> dagger g (f st₀) ≡ Abort (g st₁)
daggerProp₂ {g = g} eq = cong (dagger g) eq


starProp₁ : ∀ {f g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡  Abort st₁ -> star g (f st₀) ≡ Abort st₁
starProp₁ {g = g} eq = cong (star g) eq


correction₁ : {cmd : Expr command} -> ∀ {st st' : State} -> < cmd , st > ⇝ inj₂ (Term st') ->  [[ cmd ]] st ≡ Term st'
correction₁ (Skip st) = refl
correction₁ (Assign v e st) = refl
correction₁ (NewVar1 v e {c₀} {st₀} prf) = daggerProp₁ {[[ c₀ ]]} {λ st' → set st' v (get v st₀)}
                                        (correction₁ prf)
correction₁ (Catchin1 {c₀} {c₁} prf) = masProp₁ {[[ c₀ ]]} {[[ c₁ ]]} (correction₁ prf)


correction₂ : {cmd : Expr command} -> ∀ {st st' : State} -> < cmd , st > ⇝  inj₂ (Abort st') ->  [[ cmd ]] st ≡ Abort st'
correction₂ (Seq3 {c₀} {c₁} prf) = starProp₁ {[[ c₀ ]]} {[[ c₁ ]]} (correction₂ prf)
correction₂ (NewVar3 v e {c₀} {st₀} prf) = daggerProp₂ {[[ c₀ ]]} {λ st' → set st' v (get v st₀)}
                                        (correction₂ prf)
correction₂ Fail = refl


starProp₂ : ∀ {f g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡  Term st₁ -> star g (f st₀) ≡ g st₁
starProp₂ {g = g} eq = cong (star g) eq


starProp₃ : ∀ {f f' g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡  f' st₁ -> star g (f st₀) ≡ star g (f' st₁)
starProp₃ {g = g} eq = cong (star g) eq


masProp₂ : ∀ {f g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡  Abort st₁ -> mas g (f st₀) ≡ g st₁
masProp₂ {g = g} eq = cong (mas g) eq


masProp₃ : ∀ {f f' g : State -> Omega} {st₀ st₁ : State} -> f st₀ ≡ f' st₁ -> mas g (f st₀) ≡ mas g (f' st₁)
masProp₃ {g = g} eq  = cong (mas g) eq

{-
postulate
  ifProp₁ : ∀ {f g : State -> Omega} {e : Expr bool} {st₀ : State} -> [[ e ]] st₀ ≡ true -> f st₀ ≡ g st₀
-}

postulate
  daggerProp₃ : ∀ {f f' : State -> Omega} {g g' g'' : State -> State} {st₀ st₁ : State} -> f st₀ ≡  f' st₁ -> dagger g (f st₀) ≡ dagger g'' (f' (g' (g st₁)))



correction₃ : {c₀ c₁ : Expr command} -> ∀ {st₀ st₁ : State} -> < c₀ , st₀ > ⇝ (inj₁ < c₁ , st₁ >) ->  [[ c₀ ]] st₀ ≡ [[ c₁ ]] st₁
correction₃ (Seq1 {c₀} {c₁} prf) = starProp₂ {[[ c₀ ]]} {[[ c₁ ]]} (correction₁ prf)
correction₃ (Seq2 {c₀} {c₀'} {c₁} prf) = starProp₃ {[[ c₀ ]]} {[[ c₀' ]]} {[[ c₁ ]]} (correction₃ prf)
correction₃ (IfTrue x) = {!!}
correction₃ (IfFalse x) = {!!}
correction₃ (NewVar2 v e {c₀} {c₁} {st₀} {st₁} prf) =  daggerProp₃ {[[ c₀ ]]} {[[ c₁ ]]} {λ st' → set st' v (get v st₀)} {λ st' → set st' v (get v st₁)} {λ st' → set st' v (get v (set st₁ v (get v st₀)))} (correction₃ prf)
correction₃ (Catchin2 {c₀} {c₁} prf) = masProp₂ {[[ c₀ ]]} {[[ c₁ ]]} (correction₂ prf)
correction₃ (Catchin3 {c₀} {c₁} {c₂} prf) = masProp₃ {[[ c₀ ]]} {[[ c₁ ]]} {[[ c₂ ]]} (correction₃ prf)
