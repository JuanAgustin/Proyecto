module SemanticOp where

open import DataType
open import Data.Nat
open import Data.String
open import SemanticDen
open import Data.Bool
open import Data.Sum
open import Relation.Binary.PropositionalEquality


data _even : ℕ → Set where
  ZERO : zero even
  STEP : (x : ℕ) → x even → suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)

data IsTrue : Bool -> Set where
  isTrue  : IsTrue true
  isFalse : IsTrue false


{- Declaro las reglas que terminan, es decir que llegan a un estado final y no a otro comando  -}
{- La forma es: -}
{- < expr command , state > ----> omega -}

{-
data EvalOpTerm : Expr command -> State -> Omega -> Set where
  Skip : (st : State) -> EvalOpTerm Skip st (Term st)
  Assign : (v : String) (e : Expr nat) (st : State) -> EvalOpTerm (Assign v e) st (Term (set st v ([[ e ]] st)))
  NewVar : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ (set st₀ v ([[ e ]] st₀)) (Term st₁) -> EvalOpTerm (Newvar v e c₀) st₀ (Term (set st₁ v (get v st₀)))
  Abort1 : (st : State) -> EvalOpTerm Fail st (Abort st)
  Abort2 :  (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ st₀ (Abort st₁) -> EvalOpTerm (Seq c₀ c₁) st₀ (Abort st₁)
  catchin1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ st₀ (Term st₁) -> EvalOpTerm (Agarrame c₀ c₁) st₀ (Term st₁)
  NewVar3 : (c₀ : Expr command) (st₀ st₁ : State) (v : String) (e : Expr nat) -> EvalOpTerm c₀ st₀ (Abort st₁) -> EvalOpTerm (Newvar v e c₀) st₀ (Abort (set st₁ v (get v st₀)))

-}

{- Declaro las reglas que no terminan, es decir que continúan a otro comando -}
{- La forma es: -}
{- < expr command , state > ----> < expr command' , state' >  -}




data _⇝_ : (Expr command × State) -> (Expr command × State) ⊎ Omega -> Set where
  Skip : (st : State) -> < Skip , st > ⇝ (inj₂ (Term st))
  Assign : (v : String) (e : Expr nat) (st : State) -> < (Assign v e) , st > ⇝ (inj₂ (Term (set st v ([[ e ]] st))))
  Seq1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₂ (Term st₁)) -> < Seq c₀ c₁ , st₀ > ⇝ (inj₁ < c₁ , st₁ >)
  Seq2 : (c₀ c₁ c₀' : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₁ < c₀' , st₁ >) -> < Seq c₀ c₁ , st₀ > ⇝ (inj₁  < Seq c₀' c₁ , st₁ >)
  IfTrue : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> [[ e ]] st ≡ true -> < If e c₀ c₁ , st > ⇝ (inj₁ < c₀ , st >) 
  IfFalse : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> [[ e ]] st ≡ false -> < If e c₀ c₁ , st > ⇝ (inj₁ < c₁ , st >)
  NewVar1 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₂ (Term st₁)) -> < (Newvar v e c₀) , st₀ > ⇝  (inj₂ (Term (set st₁ v (get v st₀))))
  NewVar2 : (v : String) (e : Expr nat) (c : Expr command) (st : State) -> < Newvar v e c , st > ⇝ (inj₁ < Seq c (Assign v (const (get v st))) , (set st v ([[ e ]] st)) >)
  NewVar3 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₁ < c₁ , st₁ >) -> < (Newvar v e c₀) , st₀ > ⇝ (inj₁ < (Newvar v (const (get v st₁)) c₁) , (set st₁ v (get v st₀)) >)
  NewVar4 : (c₀ : Expr command) (st₀ st₁ : State) (v : String) (e : Expr nat) -> < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) -> < (Newvar v e c₀) , st₀ > ⇝ (inj₂ (Abort (set st₁ v (get v st₀))))
  Abort1 : (st : State) -> < Fail , st > ⇝ (inj₂ (Abort st))
  Abort2 :  (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) -> < (Seq c₀ c₁) , st₀ > ⇝ (inj₂ (Abort st₁))
  Catchin1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₂ (Term st₁)) -> < (Agarrame c₀ c₁) , st₀ > ⇝ (inj₂ (Term st₁))
  Catchin2 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) -> < (Agarrame c₀ c₁) , st₀ > ⇝ (inj₁ < c₁ ,  st₁ >)
  Catchin3 : (c₀ c₁ c₂ : Expr command) (st₀ st₁ : State) -> < c₀ , st₀ > ⇝ (inj₁ < c₁ , st₁ >) -> < (Agarrame c₀ c₂) , st₀ > ⇝ (inj₁ < (Agarrame c₁ c₂) , st₁ >)

{-
data EvalOp : (Expr command × State) -> (Expr command × State) ⊎ Omega -> Set where
  Skip : (st : State) -> EvalOp < Skip , st > (inj₂ (Term st))
  Assign : (v : String) (e : Expr nat) (st : State) -> EvalOp < (Assign v e) , st > (inj₂ (Term (set st v ([[ e ]] st))))
  Seq1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₂ (Term st₁)) -> EvalOp < Seq c₀ c₁ , st₀ > (inj₁ < c₁ , st₁ >)
  Seq2 : (c₀ c₁ c₀' : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₁ < c₀' , st₁ >) -> EvalOp < Seq c₀ c₁ , st₀ > (inj₁  < Seq c₀' c₁ , st₁ >)
  IfTrue : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOp < If e c₀ c₁ , st > (inj₁ < c₀ , st >) 
  IfFalse : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOp < If e c₀ c₁ , st > (inj₁ < c₁ , st >)
  NewVar1 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , (set st₀ v ([[ e ]] st₀)) > (inj₂ (Term st₁)) -> EvalOp < (Newvar v e c₀) , st₀ >  (inj₂ (Term (set st₁ v (get v st₀))))
  NewVar2 : (v : String) (e : Expr nat) (c : Expr command) (st : State) -> EvalOp < Newvar v e c , st > (inj₁ < Seq c (Assign v (const (get v st))) , (set st v ([[ e ]] st)) >)
  NewVar3 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , (set st₀ v ([[ e ]] st₀)) > (inj₁ < c₁ , st₁ >) -> EvalOp < (Newvar v e c₀) , st₀ > (inj₁ < (Newvar v (const (get v st₁)) c₁) , (set st₁ v (get v st₀)) >)
  NewVar4 : (c₀ : Expr command) (st₀ st₁ : State) (v : String) (e : Expr nat) -> EvalOp < c₀ , st₀ > (inj₂ (Abort st₁)) -> EvalOp < (Newvar v e c₀) , st₀ > (inj₂ (Abort (set st₁ v (get v st₀))))
  Abort1 : (st : State) -> EvalOp < Fail , st > (inj₂ (Abort st))
  Abort2 :  (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₂ (Abort st₁)) -> EvalOp < (Seq c₀ c₁) , st₀ >  (inj₂ (Abort st₁))
  Catchin1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₂ (Term st₁)) -> EvalOp < (Agarrame c₀ c₁) , st₀ > (inj₂ (Term st₁))
  Catchin2 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₂ (Abort st₁)) -> EvalOp < (Agarrame c₀ c₁) , st₀ > (inj₁ < c₁ ,  st₁ >)
  Catchin3 : (c₀ c₁ c₂ : Expr command) (st₀ st₁ : State) -> EvalOp < c₀ , st₀ > (inj₁ < c₁ , st₁ >) -> EvalOp < (Agarrame c₀ c₂) , st₀ > (inj₁ < (Agarrame c₁ c₂) , st₁ >)
-}

{-
data EvalOpCont : Expr command -> State -> Expr command -> State -> Set where
  Seq1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ st₀ (Term st₁) -> EvalOpCont (Seq c₀ c₁) st₀ c₁ st₁
  Seq2 : (c₀ c₁ c₀' : Expr command) (st₀ st₁ : State) -> EvalOpCont c₀ st₀ c₀' st₁ -> EvalOpCont (Seq c₀ c₁) st₀ (Seq c₀' c₁) st₁
  IfTrue : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOpCont (If e c₀ c₁) st c₀ st 
  IfFalse : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOpCont (If e c₀ c₁) st c₁ st  
  NewVar1 : (v : String) (e : Expr nat) (c : Expr command) (st : State) -> EvalOpCont (Newvar v e c) st (Seq c (Assign v (const (get v st)))) (set st v ([[ e ]] st))
  NewVar2 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpCont c₀ (set st₀ v ([[ e ]] st₀)) c₁ st₁ -> EvalOpCont (Newvar v e c₀) st₀ (Newvar v (const (get v st₁)) c₁) (set st₁ v (get v st₀))
  Catchin2 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ st₀ (Abort st₁) -> EvalOpCont (Agarrame c₀ c₁) st₀ c₁ st₁
  Catchin3 : (c₀ c₁ c₂ : Expr command) (st₀ st₁ : State) -> EvalOpCont c₀ st₀ c₁ st₁ -> EvalOpCont (Agarrame c₀ c₂) st₀ (Agarrame c₁ c₂) st₁
-}
