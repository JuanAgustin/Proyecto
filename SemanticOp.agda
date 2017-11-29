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

cuatro = suc (suc (suc (suc zero)))

proof₁ : cuatro even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)






{- DEFINÍ TOD0 EN UNA SOLA RELACIÓN -}

data _⇝_ : (Expr command × State) -> (Expr command × State) ⊎ Omega -> Set where
  Skip : {st : State} -> < Skip , st > ⇝ (inj₂ (Term st))
  Assign : {v : String} {e : Expr nat} {st : State} ->
         < (Assign v e) , st > ⇝ (inj₂ (Term (set st v ([[ e ]] st))))
  Seq1 : {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₂ (Term st₁)) ->
         < Seq c₀ c₁ , st₀ > ⇝ (inj₁ < c₁ , st₁ >)
  Seq2 : {c₀ c₁ c₀' : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₁ < c₀' , st₁ >) ->
         < Seq c₀ c₁ , st₀ > ⇝ (inj₁  < Seq c₀' c₁ , st₁ >)
  IfTrue : {e : Expr bool} {c₀ c₁ : Expr command} {st : State} ->
         [[ e ]] st ≡ true  ->
         < If e c₀ c₁ , st > ⇝ (inj₁ < c₀ , st >) 
  IfFalse : {e : Expr bool} {c₀ c₁ : Expr command} {st : State} ->
          [[ e ]] st ≡ false ->
          < If e c₀ c₁ , st > ⇝ (inj₁ < c₁ , st >)
  NewVar1 : {v : String} {e : Expr nat} {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
          < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₂ (Term st₁)) ->
          < (Newvar v e c₀) , st₀ > ⇝  (inj₂ (Term (set st₁ v (get v st₀))))
  NewVar2 : {v : String} {e : Expr nat} {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
          < c₀ , (set st₀ v ([[ e ]] st₀)) > ⇝ (inj₁ < c₁ , st₁ >) ->
          < (Newvar v e c₀) , st₀ > ⇝ (inj₁ < (Newvar v (const (get v st₁)) c₁) , (set st₁ v (get v st₀)) >)
  NewVar3 : {c₀ : Expr command} {st₀ st₁ : State} {v : String} {e : Expr nat} ->
          < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) ->
          < (Newvar v e c₀) , st₀ > ⇝ (inj₂ (Abort (set st₁ v (get v st₀))))
  Abort1 : {st : State} ->
         < Fail , st > ⇝ (inj₂ (Abort st))
  Abort2 :  {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
         < c₀ , st₀ > ⇝ (inj₂ (Abort st₁)) ->
         < (Seq c₀ c₁) , st₀ > ⇝ (inj₂ (Abort st₁))
  Catchin1 : {c₀ c₁ : Expr command} {st₀ st₁ : State} ->
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
proof_if₁ = Transit (CBase (IfTrue {!!})) (CBase {!Skip!})
