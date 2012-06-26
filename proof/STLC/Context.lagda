\begin{code}
module STLC.Context where

open import STLC.Base

open import Relation.Binary.PropositionalEquality

_▸▸_ : Con → Con → Con
v1 ▸▸ ε        = v1
v1 ▸▸ (y , y') = (v1 ▸▸ y) , y'

ε▸▸ : ∀ {Δ} → ε ▸▸ Δ ≡ Δ
ε▸▸ {ε} = refl
ε▸▸ {y , y'} = cong (λ v → v , y') (ε▸▸ {y})

exVar : ∀ {Γ Δ τ} → Var Γ τ → Var (Γ ▸▸ Δ) τ
exVar {Γ} {ε} v = v
exVar {Γ} {y , y'} v = vs (exVar {Γ} {y} v)

ex- : ∀ {Γ Δ τ} → (x : Var Γ τ) → (Γ - x) ▸▸ Δ ≡ (Γ ▸▸ Δ) - (exVar {Γ} {Δ} x)
ex- {Γ} {ε} x = refl
ex- {Γ} {y , y'} x = cong (λ v → v , y') (ex- {Γ} {y} x)

{-
exTm : ∀ {Γ Δ τ} → Tm Γ τ → Tm (Γ ▸▸ Δ) τ
exTm (var y) = var (exVar y)
exTm (Λ y) = Λ (wkTm vz {!!})
exTm (app y y') = app (exTm y) (exTm y')
-}

--up' {ε} {Δ} t  = up t
--up' {y , y'} t = wkTm vz {!!}\end{code}
