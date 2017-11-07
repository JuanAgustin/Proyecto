module SemanticOp where

open import DataType
open import Data.Nat
open import Data.String
open import SemanticDen
open import Data.Bool

data _even : ℕ → Set where
  ZERO : zero even
  STEP : (x : ℕ) → x even → suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)

data IsTrue : Bool -> Set where
  isTrue  : IsTrue true
  isFalse : IsTrue false


{- Declaro las reglas que terminan, es decir que llegan a un estado final y no a otro comando  -}

data EvalOpTerm : Expr command -> State -> State -> Set where
  Skip : (st : State) -> EvalOpTerm Skip st st
  Assign : (v : String) (e : Expr nat) (st : State) -> EvalOpTerm (Assign v e) st (set st v ([[ e ]] st))
  NewVar : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ (set st₀ v ([[ e ]] st₀)) st₁ -> EvalOpTerm (Newvar v e c₀) st₀ (set st₁ v (get v st₀))

{- Declaro las reglas que no terminan, es decir que continúan a otro comando -}

data EvalOpCont : Expr command -> State -> Expr command -> State -> Set where
  Seq1 : (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpTerm c₀ st₀ st₁ -> EvalOpCont (Seq c₀ c₁) st₀ c₁ st₁
  Seq2 : (c₀ c₁ c₀' : Expr command) (st₀ st₁ : State) -> EvalOpCont c₀ st₀ c₀' st₁ -> EvalOpCont (Seq c₀ c₁) st₀ (Seq c₀' c₁) st₁
  IfTrue : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOpCont (If e c₀ c₁) st c₀ st 
  IfFalse : (e : Expr bool) (c₀ c₁ : Expr command) (st : State) -> IsTrue ([[ e ]] st) -> EvalOpCont (If e c₀ c₁) st c₁ st  
  NewVar1 : (v : String) (e : Expr nat) (c : Expr command) (st : State) -> EvalOpCont (Newvar v e c) st (Seq c (Assign v (const (get v st)))) (set st v ([[ e ]] st))
  NewVar2 : (v : String) (e : Expr nat) (c₀ c₁ : Expr command) (st₀ st₁ : State) -> EvalOpCont c₀ (set st₀ v ([[ e ]] st₀)) c₁ st₁ -> EvalOpCont (Newvar v e c₀) st₀ (Newvar v (const (get v st₁)) c₁) (set st₁ v (get v st₀))
