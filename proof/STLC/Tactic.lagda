\begin{code}
module STLC.Tactic where

open import STLC.Base

infix 1 _⊢'_

data _⊢'_ : Con → Ty → Set where
  comb : ∀ {τ}     → ε ⊢ τ → ε ⊢' τ
  pure : ∀ {Γ τ}   → Γ ⊢ τ → Γ ⊢' τ
  var  : ∀ {Γ τ}   → Var Γ τ → Γ ⊢' τ
  Λ    : ∀ {Γ τ σ} → Γ , σ ⊢' τ → Γ ⊢' σ ⇒ τ
  app  : ∀ {Γ τ σ} → Γ ⊢' σ ⇒ τ → Γ ⊢' σ → Γ ⊢' τ

⟦_⟧⊢ : ∀ {Γ τ} → Γ ⊢' τ → Γ ⊢ τ
⟦ comb y ⟧⊢   = y
⟦ pure y ⟧⊢   = y
⟦ var y ⟧⊢    = var y
⟦ Λ y ⟧⊢      = Λ ⟦ y ⟧⊢
⟦ app y y' ⟧⊢ = app ⟦ y ⟧⊢ ⟦ y' ⟧⊢
\end{code}
