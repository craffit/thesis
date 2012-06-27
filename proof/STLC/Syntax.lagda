\begin{code}
module STLC.Syntax where

open import STLC.Base
open import STLC.Eval
open import STLC.SSubst

open import Relation.Binary.PropositionalEquality

infixl 3 _%·_
 
_%·_ : forall {Γ σ τ} → {t₁ t₂ : Tm Γ (σ ⇒ τ)} → {u₁ u₂ : Tm Γ σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₁ βη-≡ app t₂ u₂
_%·_ = congApp

%Λ_ : forall {Γ σ τ} → {t₁ t₂ : Tm (Γ , σ) τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
%Λ_ = congΛ

%≡_ : forall {Γ σ} → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
%≡_ = equiv

%wkTm_ : forall {Γ σ τ} → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
%wkTm_ = congWkTm

%up_ : forall {Γ τ} → {t t' : Tm ε τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
%up_ = congUp

infixl 4 _%/_

_%/_ : ∀ {Γ Δ τ} → {t t' : Tm Γ τ} → t βη-≡ t' → (s : Γ => Δ) → (t / s) βη-≡ (t' / s)
_%/_ = cong/
 
infixl 7 _⟷_

_⟷_ : forall {Γ σ} → {t₁ t₂ t₃ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
_⟷_ = btrans

□ : forall {Γ σ} → {t : Tm Γ σ} → t βη-≡ t
□ = brefl

□' : forall {Γ σ} → (t : Tm Γ σ) → t βη-≡ t
□' _ = brefl

!!_ : forall {Γ σ} → {t₁ t₂ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
!!_ = bsym

!up/ : ∀ {Γ Δ τ} → (t : Tm ε τ) → (s : Γ => Δ) → up t / s βη-≡ up t
!up/ t s = %≡ up/ t s

bind : {A : Set} {B : Set} → (a : A) → (A → B) → B
bind v f = f v 

\end{code}
