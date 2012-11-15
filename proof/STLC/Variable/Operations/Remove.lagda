\begin{code}

module STLC.Variable.Operations.Remove where

open import STLC.Variable.Operations.Subtract
open import STLC.Variable.Operations.Weaken
open import STLC.Variable.Base
open import STLC.Variable.Congruence
open import Relation.Binary.PropositionalEquality

rem : ∀ {Γ σ τ} -> (x : Γ ∋ σ) -> (y : Γ - x ∋ τ) -> Γ - (wkv x y) ∋ σ
rem vz _ = vz
rem (vs x) vz = x
rem (vs x) (vs y) = vs (rem x y)

Γ-- : ∀ {Γ σ τ} -> (x : Γ ∋ σ) -> (y : Γ - x ∋ τ) -> (Γ - x) - y ≡Γ (Γ - (wkv x y)) - (rem x y)
Γ-- vz y = ≡Γrefl
Γ-- (vs x) vz = ≡Γrefl
Γ-- (vs {σ} x) (vs y) = Γ-- x y , ≡τrefl

wkRem : ∀ {Γ σ τ} -> (x : Γ ∋ σ) -> (y : Γ - x ∋ τ) -> wkv (wkv x y) (rem x y) ≡ x
wkRem vz _ = refl
wkRem (vs _) vz = refl
wkRem (vs x) (vs y) = cong vs (wkRem x y)

wkvExc : ∀ {ρ Γ σ τ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> (v : _∋_ ((Γ - x) - y) ρ) -> wkv (wkv x y) (wkv (rem x y) (! Γ-- x y , ≡τrefl >∋ v)) ≡ wkv x (wkv y v)
wkvExc vz y _ = ≡vs (≡wkv y (!,∋-id ≡Γrefl _ _))
wkvExc (vs x) vz _ = ≡vs (≡wkv x (!,∋-id ≡Γrefl _ _))
wkvExc (vs x) (vs y) vz = ≡wkv (vs (wkv x y)) (≡wkv (vs (rem x y)) (!,∋vz (Γ-- x y) ≡τrefl _))
wkvExc (vs x) (vs y) (vs v) = ≡vs (wkvExc x y v)

\end{code}