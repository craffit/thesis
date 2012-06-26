module STLC3 where

open import Data.Unit
open import Data.Nat

-- Types
infixr 0 _⇒_
data Type : Set where
 unit : Type
 _⇒_  : Type → Type → Type

-- Contexts
infixl 4 _▸_
data Ctx : Set where
 ε   : Ctx
 _▸_ : Ctx → Type → Ctx

-- Variables
infix 0 _∋_
data _∋_ : Ctx → Type → Set where
 vz : ∀ {Γ τ}     → Γ ▸ τ ∋ τ
 vs : ∀ {Γ τ₁ τ₂} → Γ ∋ τ₁ → Γ ▸ τ₂ ∋ τ₁

infix 2 _⊑_
data _⊑_ (Γ : Ctx) : Ctx → Set where
  refl :                                        Γ ⊑ Γ
  _▻_  : {Δ : Ctx} (Γ⊑Δ : Γ ⊑ Δ) (s : Type)  → Γ ⊑ Δ ▸ s
   
-- Terms (well-scoped deBruijn)
infix 0 _⊢_
infixl 3 _·_
data _⊢_ : Ctx → Type → Set where
 t   : ∀ {Γ}      → Γ ⊢ unit
 var : ∀ {Γ τ}    → Γ ∋ τ → Γ ⊢ τ
 _·_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
 ƛ_  : ∀ {Γ τ₁ τ₂} → Γ ▸ τ₁ ⊢ τ₂ → Γ ⊢ τ₁ ⇒ τ₂

-- Interpreted Types
⟪_⟫ : Type → Set
⟪ unit    ⟫ = ⊤
⟪ τ₁ ⇒ τ₂ ⟫ = ⟪ τ₁ ⟫ → ⟪ τ₂ ⟫

-- Environments
data Env : Ctx → Set where
 ε   : Env ε
 _▸_ : ∀ {Γ τ} → Env Γ → ⟪ τ ⟫ → Env (Γ ▸ τ)

lookup : ∀ {Γ τ} → Γ ∋ τ → Env Γ → ⟪ τ ⟫
lookup vz     (ρ ▸ v) = v
lookup (vs x) (ρ ▸ v) = lookup x ρ

-- Terms (deBruijn) to interpreted Terms
⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Env Γ → ⟪ τ ⟫
⟦ t       ⟧ ρ = tt
⟦ var x   ⟧ ρ = lookup x ρ
⟦ e₁ · e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ (⟦ e₂ ⟧ ρ)
⟦ ƛ e     ⟧ ρ = λ x → ⟦ e ⟧ (ρ ▸ x)

