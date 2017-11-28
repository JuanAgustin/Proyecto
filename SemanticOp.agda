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






{- DEFINÍ TOD0 EN UNA SOLA RELACIÓN -}

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


data _⇝*_ : (Expr command × State) ⊎ Omega -> (Expr command × State) ⊎ Omega -> Set where
  Reflex : (y : (Expr command × State) ⊎ Omega) -> y ⇝* y
  CBase : (cmd : Expr command) (st : State) (y : (Expr command × State) ⊎ Omega) -> < cmd , st > ⇝ y -> (inj₁ < cmd , st >) ⇝* y  
  CInd : (y₀ y₁ y₂ : (Expr command × State) ⊎ Omega) -> y₀ ⇝* y₁ -> y₁ ⇝* y₂ -> y₀ ⇝* y₂ 


{- DEFINICION (No me dejaba usar {{ _ }}) -}
{-
¿¿_?? : {{om : Omega}} → (comm : Expr command) → (st : State) → {{p : (inj₁ < comm , st >) ⇝* (inj₂ om) }} → Omega
¿¿ comm ?? st {{ p }} = om

-}

