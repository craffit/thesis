%if False
\begin{code}
module STLC.Syntax where

open import STLC.Base
open import STLC.Equality
open import STLC.SSubst
open import STLC.Up

open import Relation.Binary.PropositionalEquality

\end{code}
%endif

\begin{code} 
%≡_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
%≡_ = equiv

%wkTm : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
%wkTm = congWkTm

%up_ : ∀ {Γ τ} → {t t' : ε ⊢ τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
%up_ = congUp

infixl 4 _%/_

_%/_ : ∀ {Γ Δ τ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → (s : Γ => Δ) → t / s βη-≡ t' / s
_%/_ = cong/

□' : ∀ {Γ σ} → (t : Γ ⊢ σ) → t βη-≡ t
□' _ = brefl

!!_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
!!_ = bsym

!up/ : ∀ {Γ Δ τ} → (t : ε ⊢ τ) → (s : Γ => Δ) → up t / s βη-≡ up t
!up/ t s = %≡ up/ t s

bind : {A : Set} {B : Set} → (a : A) → (A → B) → B
bind v f = f v 

\end{code}
