\begin{code}

module STLC.Variable.Congruence where

open import STLC.Variable.Base
open import STLC.Context.Equality public
open import Relation.Binary.PropositionalEquality

infix 11 !_,_>∋_
infix 11 ≡!_,_>∋_

!_,_>∋_ : ∀ {Γ Δ τ σ} → Γ ≡Γ Δ → τ ≡τ σ → (y : Γ ∋ τ) → Δ ∋ σ
! ε , p2 >∋ ()
! (p1 , p3) , p2 >∋ vz with ≡τ-≡ (≡τtrans (≡τsym p3) p2)
! (p1 , p3) , p2 >∋ vz | refl = vz
! (p1 , p3) , p2 >∋ vs y = vs (! p1 , p2 >∋ y)

≡!_,_>∋_ : ∀ {Γ Δ τ σ} → {g g' : Γ ≡Γ Δ} → {t t' : τ ≡τ σ} → {y y' : Γ ∋ τ} →
         g ≡ g' → t ≡ t' → y ≡ y' → ! g , t >∋ y ≡ ! g' , t' >∋ y'
≡! refl , refl >∋ refl = refl         

!,∋-id : ∀ {Γ τ} → (p : Γ ≡Γ Γ) → (p' : τ ≡τ τ) → (y : Γ ∋ τ) → ! p , p' >∋ y ≡ y
!,∋-id ε p' ()
!,∋-id (p1 , p2) p' vz with ≡τ-≡ (≡τtrans (≡τsym p2) p')
... | refl = refl
!,∋-id (p1 , p2) p' (vs y) = cong vs (!,∋-id p1 p' y)

!,∋vz : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p p' : τ ≡τ σ) → ! (p1 , p) , p' >∋ vz ≡ vz 
!,∋vz p1 p p' with ≡τ-≡ (≡τtrans (≡τsym p) p')
... | refl = refl

!,∋vz-flip : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p : τ ≡τ σ) → ! (p1 , ≡τrefl) , p >∋ vz ≡ ! (p1 , ≡τsym p) , ≡τrefl >∋ vz 
!,∋vz-flip p1 p with ≡τ-≡ p
!,∋vz-flip p1 p | refl with ≡τ-eq-refl p
!,∋vz-flip p1 .≡τrefl | refl | refl = cong (λ v → ! (p1 , v) , ≡τrefl >∋ vz) (≡τ-eq-eq _ _)

\end{code}