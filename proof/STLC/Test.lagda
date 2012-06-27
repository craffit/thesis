\begin{code}
module STLC.Syntax where

open import STLC.Base
open import STLC.Eval
open import STLC.SSubst

open import Relation.Binary.PropositionalEquality

infixl 3 _%·_
 
_%·_ : forall {G σ τ} → {t₁ t₂ : Tm G (σ ⇒ τ)} → {u₁ u₂ : Tm G σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₁ βη-≡ app t₂ u₂
_%·_ = congApp


\end{code}
