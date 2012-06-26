module STLC2 where

infixl 70 _·_
infix  50 ƛ_
infixr 30 _⟶_

data Ty : Set where
  base : Ty
  _⟶_  : (σ τ : Ty) → Ty

data Tm' (V : Ty → Set) : Ty → Set where
  var : ∀ {σ}   (x : V σ) → Tm' V σ
  ƛ_  : ∀ {σ τ} (t : V σ → Tm' V τ) → Tm' V (σ ⟶ τ)
  _·_ : ∀ {σ τ} (t₁ : Tm' V (σ ⟶ τ)) (t₂ : Tm' V σ) → Tm' V τ

Tm : Ty → Set1
Tm σ = ∀ {V} → Tm' V σ

Val' : (Ty → Set) → Ty → Set
Val' B base    = B base
Val' B (σ ⟶ τ) = Val' B σ → Val' B τ

Val : Ty → Set1
Val σ = ∀ {V} → Val' V σ

⟦_⟧' : ∀ {B τ} → Tm' (Val' B) τ → Val' B τ
⟦ var x   ⟧' = x
⟦ ƛ t     ⟧' = λ x → ⟦ t x ⟧'
⟦ t₁ · t₂ ⟧' = ⟦ t₁ ⟧' ⟦ t₂ ⟧'

⟦_⟧ : ∀ {τ} → Tm τ → Val τ
⟦ t ⟧ = ⟦ t ⟧'
