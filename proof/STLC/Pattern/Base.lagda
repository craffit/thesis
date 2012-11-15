\begin{code}

open import STLC

module STLC.Pattern.Base where

open import STLC
open import Util.PropositionalEquality

data Pat (Γ Γ' : Con) : (τ : Ty) → Set where
  var   : ∀ {τ}  → (v : Γ ∋ τ) → Pat Γ Γ' τ
  pvar  : ∀ {τ}   → (v : Γ' ∋ τ) → Pat Γ Γ' τ
  _·_   : ∀ {σ τ} → Pat Γ Γ' (σ ⇒ τ) → Pat Γ Γ' σ → Pat Γ Γ' τ

patApp : ∀ {Γ Γ' τ} → Pat Γ Γ' τ → Γ' => Γ → Γ ⊢ τ
patApp (var v) s  = var v
patApp (pvar v) s = lookup v s
patApp (y · y') s = patApp y s · patApp y' s
\end{code}