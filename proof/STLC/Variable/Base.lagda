\begin{code}

module STLC.Variable.Base where

open import STLC.Context.Base public
open import Relation.Binary.PropositionalEquality

infix 4 _∋_ 

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ σ}    → Γ , σ ∋ σ
  vs : ∀ {τ Γ σ}  → Γ ∋ σ → Γ , τ ∋ σ

vs-inj : ∀ {τ Γ σ} → {i j : Γ ∋ σ} → vs {τ} i ≡ vs j → i ≡ j
vs-inj refl = refl

≡vs : ∀ {σ Γ τ} {e1 e2 : Γ ∋ τ} → e1 ≡ e2 → vs {σ} e1 ≡ vs {σ} e2
≡vs = cong vs

\end{code}