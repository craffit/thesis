%if False
\begin{code}
module STLC.Syntax where

open import STLC.Base
open import STLC.Equality
open import STLC.SSubst
open import STLC.Up

open import Relation.Binary.PropositionalEquality

infixl 3 _%·_
\end{code}
%endif

\begin{code} 
_%·_ : ∀ {Γ σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → t₁ · u₁ βη-≡ t₂ · u₂
_%·_ = congApp

%Λ_ : ∀ {Γ σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
%Λ_ = congΛ

%≡_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
%≡_ = equiv

%wkTm_ : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
%wkTm_ = congWkTm

%up_ : ∀ {Γ τ} → {t t' : ε ⊢ τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
%up_ = congUp

infixl 4 _%/_

_%/_ : ∀ {Γ Δ τ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → (s : Γ => Δ) → t / s βη-≡ t' / s
_%/_ = cong/
 
infixl 7 _⟷_

_⟷_ : ∀ {Γ σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
_⟷_ = btrans

□ : ∀ {Γ σ} → {t : Γ ⊢ σ} → t βη-≡ t
□ = brefl

□' : ∀ {Γ σ} → (t : Γ ⊢ σ) → t βη-≡ t
□' _ = brefl

!!_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
!!_ = bsym

!up/ : ∀ {Γ Δ τ} → (t : ε ⊢ τ) → (s : Γ => Δ) → up t / s βη-≡ up t
!up/ t s = %≡ up/ t s

bind : {A : Set} {B : Set} → (a : A) → (A → B) → B
bind v f = f v 

\end{code}
