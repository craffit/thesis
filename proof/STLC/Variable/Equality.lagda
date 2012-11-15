\begin{code}

module STLC.Variable.Equality where

open import STLC.Variable.Operations
open import Relation.Binary.PropositionalEquality

data EqV {Γ : Con} : {σ τ : Ty} → Γ ∋ σ → Γ ∋ τ → Set where
  same : ∀ {σ} → {x : Γ ∋ σ} → EqV x x
  diff : ∀ {σ τ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → EqV x (wkv x y)

eq : ∀ {Γ σ τ} → (x : Γ ∋ σ) → (y : Γ ∋ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)

eq-same-vs : ∀ {Γ σ τ} → (x : Γ ∋ σ) → eq x x ≡ same → eq (vs {τ} x) (vs x) ≡ same
eq-same-vs x p with eq x x
eq-same-vs x refl | .same = refl

eq-same : ∀ {Γ σ} → (x : Γ ∋ σ) → eq x x ≡ same
eq-same vz = refl
eq-same (vs x) = eq-same-vs x (eq-same x)

eq-diff-vs : ∀ {Γ σ τ ρ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → eq x (wkv x y) ≡ diff x y 
           → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
eq-diff-vs x y p with eq x (wkv x y)
eq-diff-vs x y refl | .(diff x y) = refl

eq-diff : ∀ {Γ σ τ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → eq x (wkv x y) ≡ diff x y
eq-diff vz y = refl
eq-diff (vs x) vz = refl
eq-diff (vs x) (vs y) = eq-diff-vs x y (eq-diff x y)
\end{code}