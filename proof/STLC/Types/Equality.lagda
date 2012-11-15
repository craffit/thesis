\begin{code}
module STLC.Types.Equality where

open import STLC.Types.Base
open import Data.Nat

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary using (Decidable)

infix 1 _≡τ_

data _≡τ_ : (τ : Ty) → (τ' : Ty) → Set where
  C     : (y : ℕ) → C y ≡τ C y
  _⇒_   : ∀ {τ σ τ' σ'} → (p1 : τ ≡τ τ') → (p2 : σ ≡τ σ') → τ ⇒ σ ≡τ τ' ⇒ σ'

≡τ⇒left : ∀ {σ σ' τ τ'} → σ ⇒ τ ≡τ σ' ⇒ τ' → σ ≡τ σ'
≡τ⇒left (p1 ⇒ p2) = p1

≡τ⇒right : ∀ {σ σ' τ τ'} → σ ⇒ τ ≡τ σ' ⇒ τ' → τ ≡τ τ'
≡τ⇒right (p1 ⇒ p2) = p2

≡τ-≡ : {τ τ' : Ty} → τ ≡τ τ' → τ ≡ τ'
≡τ-≡ (C y) = refl
≡τ-≡ (p1 ⇒ p2) = cong₂ _⇒_ (≡τ-≡ p1) (≡τ-≡ p2)

≡-≡τ : {τ τ' : Ty} → τ ≡ τ' → τ ≡τ τ'
≡-≡τ {.(C y)} {C y} refl = C y
≡-≡τ {.(y ⇒ y')} {y ⇒ y'} refl = ≡-≡τ refl ⇒ ≡-≡τ refl

≡τrefl : {τ : Ty} → τ ≡τ τ
≡τrefl {C y} = C y
≡τrefl {y ⇒ y'} = ≡τrefl ⇒ ≡τrefl

≡τsym : {τ τ' : Ty} → τ ≡τ τ' → τ' ≡τ τ
≡τsym (C y) = C y
≡τsym (p1 ⇒ p2) = ≡τsym p1 ⇒ ≡τsym p2

≡τtrans : {τ τ' τ'' : Ty} → τ ≡τ τ' → τ' ≡τ τ'' → τ ≡τ τ''
≡τtrans (C y) p2 = p2
≡τtrans (p1 ⇒ p2) (p3 ⇒ p4) = ≡τtrans p1 p3 ⇒ ≡τtrans p2 p4

≡-≡τ-id : {τ τ' : Ty} → (x : τ ≡ τ') → ≡τ-≡ (≡-≡τ x) ≡ x
≡-≡τ-id {.(C y)} {C y} refl = refl
≡-≡τ-id {.(y ⇒ y')} {y ⇒ y'} refl = cong₂ (cong₂ _⇒_) (≡-≡τ-id {y} {y} refl) (≡-≡τ-id {y'} {y'} refl)

≡τ-eq-refl : {τ : Ty} → (x : τ ≡τ τ) → x ≡ ≡τrefl
≡τ-eq-refl (C y) = refl
≡τ-eq-refl (p1 ⇒ p2) = cong₂ _⇒_ (≡τ-eq-refl p1) (≡τ-eq-refl p2)

≡τ-eq-eq : ∀ {τ τ'} → (p p2 : τ ≡τ τ') → p ≡ p2
≡τ-eq-eq p p2 with ≡τ-≡ p
... | refl = trans (≡τ-eq-refl p) (sym (≡τ-eq-refl p2))

_≟τ_ : Decidable {A = Ty} _≡_
C y ≟τ C y' with y ≟ y'
C y ≟τ C y' | yes p = yes (≡C p)
C y ≟τ C y' | no ¬p = no (λ x → ¬p (inj-C x))
C y ≟τ (y' ⇒ y0) = no (λ ())
(y ⇒ y') ≟τ C y0 = no (λ ())
(y ⇒ y') ≟τ (y0 ⇒ y1) with y ≟τ y0 | y' ≟τ y1
(y ⇒ y') ≟τ (y0 ⇒ y1) | yes p | yes p' = yes (p ≡⇒ p')
(y ⇒ y') ≟τ (y0 ⇒ y1) | yes p | no ¬p = no (λ refl' → ¬p (⇒-inj-right refl'))
(y ⇒ y') ≟τ (y0 ⇒ y1) | no ¬p | yes p = no (λ refl' → ¬p (⇒-inj-left refl'))
(y ⇒ y') ≟τ (y0 ⇒ y1) | no ¬p | no ¬p' = no (λ refl' → ¬p (⇒-inj-left refl'))

\end{code}