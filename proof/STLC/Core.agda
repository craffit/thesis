module STLC.Core where
{-
-- Types
infixr 0 _⇒_
data Type : Set where
 _⇒_  : Type → Type → Type

-- Contexts
infixl 4 _▸_
data Ctx : Set where
 ε   : Ctx
 _▸_ : Ctx → Type → Ctx

infixl 4 _▸▸_
_▸▸_ : Ctx → Ctx → Ctx
Γ ▸▸ ε       = Γ
Γ ▸▸ (Δ ▸ s) = Γ ▸▸ Δ ▸ s

-- Variables
infix 0 _∋_
data _∋_ : Ctx → Type → Set where
 vz : ∀ {Γ τ}     → Γ ▸ τ ∋ τ
 vs : ∀ {Γ τ₁ τ₂} → Γ ∋ τ₁ → Γ ▸ τ₂ ∋ τ₁
   
-- Terms (well-scoped deBruijn)
infix 0 _⊢_
infixl 3 _·_
data _⊢_ : Ctx → Type → Set where
  var   : ∀ {τ}        → ε ⊢ τ
  _·_   : ∀ {Γ τ₁ τ₂}   → Γ ⊢ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
  ƛ_    : ∀ {Γ τ₁ τ₂}   → Γ ▸ τ₁ ⊢ τ₂ → Γ ⊢ τ₁ ⇒ τ₂
  wk    : ∀ {Γ τ₁ τ₂}   → Γ ⊢ τ₂ → Γ ▸ τ₁ ⊢ τ₂
  subst : ∀ {Γ τ₁ τ₂}   → Γ ⊢ τ₁ → Γ ∋ τ₂ → Γ ⊢ τ₁

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
⟦ var ⟧ = var
⟦ y · y' ⟧ with ⟦ y ⟧ | ⟦ y' ⟧
... | ƛ v   | v2    = {!subst v !}
... | wk v1 | wk v2 = wk (v1 · v2)
... | v1    | v2    = v1 · v2
⟦ ƛ y ⟧ = {!!}
⟦ wk y ⟧ = {!!}
⟦ subst y y' ⟧ = {!!}
-}
{-
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

-}

module STLC3 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Types
infixr 0 _⇒_
data Type : Set where
 _⇒_  : Type → Type → Type

-- Contexts
infixl 4 _▸_
data Ctx : Set where
 ε   : Ctx
 _▸_ : Ctx → Type → Ctx

infixl 4 _▸▸_
_▸▸_ : Ctx → Ctx → Ctx
Γ ▸▸ ε = Γ
Γ ▸▸ (Δ ▸ τ) = (Γ ▸▸ Δ) ▸ τ

▸▸-left-id : ∀ {Γ} → ε ▸▸ Γ ≡ Γ
▸▸-left-id {ε} = refl
▸▸-left-id {y ▸ y'} = cong (λ v → v ▸ y') (▸▸-left-id {y})

▸▸-assoc : ∀ Γ₁ Γ₂ Γ₃ → (Γ₁ ▸▸ Γ₂) ▸▸ Γ₃ ≡ Γ₁ ▸▸ (Γ₂ ▸▸ Γ₃)
▸▸-assoc Γ₁ Γ₂ ε = refl
▸▸-assoc Γ₁ Γ₂ (y ▸ y') = cong (λ v → v ▸ y') (▸▸-assoc Γ₁ Γ₂ y)

-- Terms (well-scoped deBruijn)
infix 0 _⊢_
infixl 3 _·_
data _⊢_ : Ctx → Type → Set where
 var : ∀ {Γ τ}     → Γ ▸ τ ⊢ τ
 lf  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ▸ τ₂ ⊢ τ₁
 _·_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
 ƛ_  : ∀ {Γ τ₁ τ₂} → Γ ▸ τ₁ ⊢ τ₂ → Γ ⊢ τ₁ ⇒ τ₂

{-
up' : ∀ {Δ Γ τ} → Γ ⊢ τ → Δ ▸▸ Γ ⊢ τ
up' {ε} {Γ} {τ} v  = subst (λ v' → v' ⊢ τ) (sym ▸▸-left-id) v
up' {y ▸ y'} {Γ} {τ} v = subst (λ v' → v' ⊢ τ) (sym (▸▸-assoc y (ε ▸ y') Γ))
                           (up' {y} {ε ▸ y' ▸▸ Γ} (wk v))
-}
up : ∀ {Δ τ} → ε ⊢ τ → Δ ⊢ τ
up {ε} v      = v
up {y ▸ y'} v = lf (up v)

--- wk : ∀ {Δ τ τ₂} → ε ▸▸ Δ ⊢ τ → ε ▸ τ₂ ▸▸ Δ ⊢ τ
-- wk {Δ} = lf {ε} {Δ}

{-
_↑ : ∀ {Γ τ} → ε ⊢ τ → Γ ⊢ τ
_↑ {ε}      v = v
_↑ {y ▸ y'} v = wk (_↑ v)
-}
{-
_↑ : ∀ {Δ Γ τ} → Γ ⊢ τ → Γ ▸▸ Δ ⊢ τ
_↑ {ε} v      = v
_↑ {y ▸ y'} v = wk {_} {_} {y'} (_↑ {y} v)
-}

-- Interpreted Types
⟪_⟫ : Type → Set
⟪ τ₁ ⇒ τ₂ ⟫ = ⟪ τ₁ ⟫ → ⟪ τ₂ ⟫

-- Environments
data Env : Ctx → Set where
 ε   : Env ε
 _►_ : ∀ {Γ τ} → Env Γ → ⟪ τ ⟫ → Env (Γ ▸ τ)

{-
shrink : ∀ {Γ τ} → Env (ε ▸ τ ▸▸ Γ) → Env Γ
shrink {ε} (y ▸ y') = y
shrink {y ▸ y'} {τ} (y0 ▸ y1) = shrink y0 ▸ y1
-}
-- Terms (deBruijn) to interpreted Terms
⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Env Γ → ⟪ τ ⟫
⟦ var ⟧     (_ ► v)  = v
⟦ lf e ⟧    (ρ ► _)  = ⟦ e ⟧ ρ
⟦ e₁ · e₂ ⟧  ρ        = ⟦ e₁ ⟧ ρ (⟦ e₂ ⟧ ρ)
⟦ ƛ e     ⟧ ρ        = λ x → ⟦ e ⟧ (ρ ► x)

