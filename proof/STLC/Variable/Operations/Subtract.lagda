%if False
\begin{code}

module STLC.Variable.Operations.Subtract where

open import STLC.Variable.Base public
open import STLC.Context.Equality
open import STLC.Variable.Congruence
open import Relation.Binary.PropositionalEquality

infixl 5 _-_ 

\end{code}
%endif

\begin{code}
_-_ : {σ : Ty} → (Γ : Con) → Γ ∋ σ → Con
ε      - ()
Γ , σ  - vz    = Γ
Γ , τ  - vs x  = (Γ - x) , τ
\end{code}

%if False
\begin{code}
-≡Γ : ∀ {Γ Δ τ σ} → (p : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (v : Γ ∋ τ) 
      → Γ - v ≡Γ Δ - (! p , p2 >∋ v)
-≡Γ ε p2 ()
-≡Γ (p1 , p2) p vz with ≡τ-≡ (≡τtrans (≡τsym p2) p)
-≡Γ (p1 , p2) p vz | refl = p1
-≡Γ (p1 , p2) p (vs y) with ≡τ-≡ p2
... | refl = (-≡Γ p1 p y) , ≡τrefl

-≡Γvz : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (-≡Γ (p1 , p2) p2 vz) ≡ (subst (\v → Γ ≡Γ (Δ , σ - v)) (sym (!,∋vz p1 p2 p2)) p1) 
-≡Γvz p p2 with ≡τ-≡ (≡τtrans (≡τsym p2) p2)
... | refl = refl

-≡Γvs : ∀ {Γ Δ σ σ' τ τ'} → (p : Γ ≡Γ Δ) → (p2 : τ ≡τ τ') → (p3 : σ ≡τ σ')
      → (v : Γ ∋ σ) → (-≡Γ (p , p2) p3 (vs v)) ≡ ((-≡Γ p p3 v) , p2)
-≡Γvs p p2 p3 v with ≡τ-≡ p2
... | refl = cong (_,_ (-≡Γ p p3 v)) (sym (≡τ-eq-refl p2))

\end{code}
%endif