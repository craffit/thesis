%if False
\begin{code}
module STLC.Term.Operations.Up where

open import STLC.Term.Base
open import STLC.Term.Operations.Weaken
open import STLC.Term.Operations.Simultaneous
open import Util.PropositionalEquality
open import STLC.Term.Convertibility
\end{code}
%endif

\begin{code}
up : ∀ {Γ τ} → ε ⊢ τ → Γ ⊢ τ
up t = t / sz
\end{code}

%if False
\begin{code}
up-id : ∀ {Γ Δ τ} → (v : ε ⊢ τ) → (s : Γ => Δ) → up v / s ≡ up v
up-id v s = merge-/ v sz s

%up : ∀ {Γ τ} {e e' : ε ⊢ τ} → e βη-≡ e' → up {Γ} e βη-≡ up e'
%up eq = eq %/- sz

wk-up : ∀ {Γ τ σ} → (v : Γ ∋ σ) → (e : ε ⊢ τ) → wkTm v (up e) ≡ up e
wk-up v e = sym (wk/ v e sz)
\end{code}
%endif