\begin{code}
module STLC.Context.Equality where

open import STLC.Types.Equality
open import STLC.Context.Base

open import Relation.Binary.PropositionalEquality

infix 1 _≡Γ_

data _≡Γ_ : (Γ : Con) → (Δ : Con) → Set where
  ε     : ε ≡Γ ε
  _,_   : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → Γ , τ ≡Γ Δ , σ

≡Γ-≡ : ∀ {Γ Δ} → Γ ≡Γ Δ → Γ ≡ Δ
≡Γ-≡ ε = refl
≡Γ-≡ (p1 , p2) = cong₂ _,_ (≡Γ-≡ p1) (≡τ-≡ p2)

≡-≡Γ : ∀ {Γ Δ} → Γ ≡ Δ → Γ ≡Γ Δ
≡-≡Γ {.ε} {ε} refl = ε
≡-≡Γ {.(y , y')} {y , y'} refl = ≡-≡Γ refl , ≡-≡τ refl

≡Γrefl : ∀ {Γ} → Γ ≡Γ Γ
≡Γrefl {ε} = ε
≡Γrefl {y , y'} = ≡Γrefl , ≡τrefl

≡Γsym : ∀ {Γ Δ} → Γ ≡Γ Δ → Δ ≡Γ Γ
≡Γsym ε = ε
≡Γsym (p1 , p2) = ≡Γsym p1 , ≡τsym p2

≡Γtrans : {Γ Δ Δ' : Con} → Γ ≡Γ Δ → Δ ≡Γ Δ' → Γ ≡Γ Δ'
≡Γtrans ε ε = ε
≡Γtrans (p1 , p2) (p3 , p4) = ≡Γtrans p1 p3 , ≡τtrans p2 p4

≡-≡Γ-id : {Γ Δ : Con} → (x : Γ ≡ Δ) → ≡Γ-≡ (≡-≡Γ x) ≡ x
≡-≡Γ-id {.ε} {ε} refl = refl
≡-≡Γ-id {.(y , y')} {y , y'} refl = cong₂ (cong₂ _,_) (≡-≡Γ-id {y} {y} refl) (≡-≡τ-id {y'} {y'} refl)

≡Γ-eq-refl : {Γ : Con} → (x : Γ ≡Γ Γ) → x ≡ ≡Γrefl
≡Γ-eq-refl ε = refl
≡Γ-eq-refl (p1 , p2) = cong₂ _,_ (≡Γ-eq-refl p1) (≡τ-eq-refl p2)

≡Γ-eq-eq : {Γ Δ : Con} → (p1 p2 : Γ ≡Γ Δ) → p1 ≡ p2
≡Γ-eq-eq p1 p2 with ≡Γ-≡ p1
... | refl = trans (≡Γ-eq-refl p1) (sym (≡Γ-eq-refl p2))

\end{code}
