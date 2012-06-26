\begin{code}
{-# OPTIONS --termination-depth=1 #-}
module STLC.Core2 where
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
--  subst : ∀ {Γ τ₁ τ₂}   → Γ ⊢ τ₁ → Γ ∋ τ₂ → Γ ⊢ τ₁

{-
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

-- Variables
infix 0 _∋_
data _∋_ : Ctx → Type → Set where
 vz : ∀ {Γ τ}     → Γ ▸ τ ∋ τ
 vs : ∀ {Γ τ₁ τ₂} → Γ ∋ τ₁ → Γ ▸ τ₂ ∋ τ₁

_-_ : {σ : Type} → (Γ : Ctx) → Γ ∋ σ → Ctx
ε       - ()
(Γ ▸ σ) - vz     = Γ
(Γ ▸ τ) - (vs x) = (Γ - x) ▸ τ
   
-- Terms (well-scoped deBruijn)
infix 0 _⊢_
infixl 3 _·_
data _⊢_ : Ctx → Type → Set where
 var   : ∀ {Γ τ}    → Γ ▸ τ ⊢ τ
 lf    : ∀ {Γ τ₁ τ₂} → (x : Γ ∋ τ₂) → Γ - x ⊢ τ₁ → Γ ⊢ τ₁
-- wk    : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ▸ τ₂ ⊢ τ₁
 _·_   : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
 ƛ_    : ∀ {Γ τ₁ τ₂} → Γ ▸ τ₁ ⊢ τ₂ → Γ ⊢ τ₁ ⇒ τ₂

           
{-
up' : ∀ {Δ Γ τ} → Γ ⊢ τ → Δ ▸▸ Γ ⊢ τ
up' {ε} {Γ} {τ} v  = subst (λ v' → v' ⊢ τ) (sym ▸▸-left-id) v
up' {y ▸ y'} {Γ} {τ} v = subst (λ v' → v' ⊢ τ) (sym (▸▸-assoc y (ε ▸ y') Γ))
                           (up' {y} {ε ▸ y' ▸▸ Γ} (wk v))
-}
{-
up : ∀ {Δ τ} → ε ⊢ τ → Δ ⊢ τ
up {ε} v      = v
up {y ▸ y'} v = lf vz (up v)
-}
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
 _►_ : ∀ {Γ τ} → Env Γ → Γ ⊢ τ → Env (Γ ▸ τ)

{-
shrink : ∀ {Γ τ} → Env (ε ▸ τ ▸▸ Γ) → Env Γ
shrink {ε} (y ▸ y') = y
shrink {y ▸ y'} {τ} (y0 ▸ y1) = shrink y0 ▸ y1
-}
{-
sub : ∀ {Δ Γ τ₁ τ₂} → Γ ▸▸ Δ ⊢ τ₂ → (x : Γ ∋ τ₁) → (Γ - x) ▸▸ Δ ⊢ τ₁ → (Γ - x) ▸▸ Δ ⊢ τ₂
sub {ε} var vz u = u
sub {ε} var (vs y) u = var
sub {y ▸ τ₂} var vz u = {!!}
sub {y ▸ τ₂} var (vs y') u = {!!}
sub {ε} (lf y) t u = {!!}
sub {y ▸ y'} (lf y0) t u = {!!}
sub {y} (y0 · y1) t u = {!!}
sub {y} (ƛ y0) t u = {!!}
-}

{-
sub : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₂ → (x : Γ ∋ τ₁) → Γ - x ⊢ τ₁ → Γ - x ⊢ τ₂
sub var vz u = u
sub var (vs ()) u
sub (lf vz y) vz u = y
sub (lf (vs y) y') vz u = lf y (ƛ y') · u
sub (lf vz y) (vs y') u = sub (wk y) (vs y') u
sub (lf (vs y) y') (vs y0) u = sub (wk y') {!!} (ƛ u)
sub (wk y) v u = {!!}
sub (y · y') v u = {!!}
sub (ƛ y) v u = {!!}   
-}


wkv : forall {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ∋ τ → Γ ∋ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)


{-
wkv : forall {Γ σ τ} → (x : Γ ∋ τ) → Γ ▸ σ ∋ τ 
wkv vz = {!!}
wkv (vs y) = {!!}

wkTm : forall {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm vz var = lf var
wkTm vz (lf y) = lf (lf y)
wkTm vz (y · y') = lf (y · y')
wkTm vz (ƛ y) = lf (ƛ y)
wkTm (vs y) var = var
wkTm (vs y) (lf y') = lf (wkTm y y')
wkTm (vs y) (y' · y0) = wkTm (vs y) y' · wkTm (vs y) y0
wkTm (vs y) (ƛ y') = ƛ wkTm (vs (vs y)) y'
-}

{-
wkTm {Γ} x p = ?
wkTm x (lf v) = ?
wkTm x (ƛ t) = ƛ (wkTm (vs x) t)
wkTm x (t₁ · t₂) = wkTm x t₁ · wkTm x t₂
-}

sub : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₂ → (x : Γ ∋ τ₁) → Γ - x ⊢ τ₁ → Γ - x ⊢ τ₂
sub var vz u            = u
sub var (vs y) u        = var
sub (lf vz y) vz u      = y
sub (lf (vs y) y') vz u = lf y (ƛ y') · u
sub (lf vz y) (vs y') u = lf vz (sub {!!} vz (ƛ u))
sub (lf (vs y) y') (vs y0) u = {!!}
sub (y · y') x u = sub y x u · sub y' x u
sub (ƛ y) x u    = ƛ sub y (vs x) (lf vz u)

-- Terms (deBruijn) to interpreted Terms
⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
⟦ var ⟧     = var
⟦ lf v e ⟧  = lf v ⟦ e ⟧
⟦ e₁ · e₂ ⟧ with ⟦ e₁ ⟧ | ⟦ e₂ ⟧
⟦ e₁ · e₂ ⟧ | ƛ e₁'  | e₂'     = sub e₁' vz e₂'
⟦ e₁ · e₂ ⟧ | e₁'    | e₂'     = e₁' · e₂'
⟦ ƛ e     ⟧ = ƛ ⟦ e ⟧

\end{code}
