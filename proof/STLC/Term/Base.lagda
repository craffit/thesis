\begin{code}

module STLC.Term.Base where

open import STLC.Variable public
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary.Decidable

open import Data.Nat
open import Data.Fin hiding (_-_)

infix 2 _⊢_
infixl 10 _·_
infixl 10 _≡·_    

data _⊢_ : Con → Ty → Set where
  var  : ∀ {Γ σ}    → Γ ∋ σ → Γ ⊢ σ
  Λ    : ∀ {σ Γ τ}  → Γ , σ ⊢ τ → Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ Γ τ}  → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ

≡var : ∀ {Γ τ} {e1 e2 : Γ ∋ τ} → e1 ≡ e2 → var e1 ≡ var e2
≡var = cong var

≡Λ : ∀ {Γ σ τ} {f1 f2 : Γ , σ ⊢ τ} → f1 ≡ f2 → Λ f1 ≡ Λ f2
≡Λ = cong Λ

_≡·_ : ∀ {Γ σ τ} {f1 f2 : Γ ⊢ σ ⇒ τ} {a1 a2 : Γ ⊢ σ} → f1 ≡ f2
     → a1 ≡ a2 → f1 · a1 ≡ f2 · a2
_≡·_ = cong₂ _·_

var-inj : ∀ {Γ τ} {e1 e2 : Γ ∋ τ} → var e1 ≡ var e2 → e1 ≡ e2
var-inj refl = refl

Λ-inj : ∀ {Γ σ τ} {f1 f2 : Γ , σ ⊢ τ} → Λ f1 ≡ Λ f2 → f1 ≡ f2
Λ-inj refl = refl

·-inj-index : ∀ {Γ σ σ' τ} → {f : Γ ⊢ σ ⇒ τ} → {f' : Γ ⊢ σ' ⇒ τ} → {a : Γ ⊢ σ}
            → {a' : Γ ⊢ σ'} → f · a ≡ f' · a' → σ ≡ σ'
·-inj-index refl = refl

·-inj-left : ∀ {Γ σ τ} → {f f' : Γ ⊢ σ ⇒ τ} → {a a' : Γ ⊢ σ} → f · a ≡ f' · a' 
           → f ≡ f'
·-inj-left refl = refl

·-inj-right : ∀ {Γ σ τ} → {f f' : Γ ⊢ σ ⇒ τ} → {a a' : Γ ⊢ σ} → f · a ≡ f' · a' 
           → a ≡ a'
·-inj-right refl = refl

v : (m : ℕ) → {Γ : Con} → {m<n : True (suc m ≤? size Γ)} → Γ ⊢ ind Γ (#_ m {size Γ} {m<n})
v x = var (i x)

\end{code}