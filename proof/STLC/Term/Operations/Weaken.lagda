%if False
\begin{code}

module STLC.Term.Operations.Weaken where

open import STLC.Term.Base public
open import STLC.Term.Congruence
open import STLC.Variable
open import Util.PropositionalEquality
open import Relation.Nullary
open ≡-Reasoning

\end{code}
%endif

\begin{code}
wkTm : ∀ {σ Γ τ} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm x (var v)    = var (wkv x v)
wkTm x (Λ t)      = Λ (wkTm (vs x) t)
wkTm x (t₁ · t₂)  = wkTm x t₁ · wkTm x t₂

weaken : ∀ {σ Γ τ} → Γ ⊢ τ → Γ , σ ⊢ τ
weaken t = wkTm vz t

\end{code}

%if False
\begin{code}

≡wkTm :  ∀ {σ Γ τ} → (x : Γ ∋ σ) → {e e' : Γ - x ⊢ τ} → e ≡ e'
      → wkTm x e ≡ wkTm x e'
≡wkTm x = cong (wkTm x)

≡weaken :  ∀ {σ Γ τ} → {e e' : Γ ⊢ τ} → e ≡ e'
        → weaken {σ} e ≡ weaken {σ} e'
≡weaken = cong weaken

!,⊢wkTm : ∀ {Γ Δ τ σ a b} → (v : Γ ∋ a) → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) 
        → (p3 : a ≡τ b) → (t : Γ - v ⊢ τ) 
        → ! p1 , p2 >⊢ wkTm v t 
        ≡ wkTm (! p1 , p3 >∋ v) (! (-≡Γ p1 p3 v) , p2 >⊢ t)
!,⊢wkTm v p1 p2 p3 (var y) = cong var (!,∋-wkv v p1 p2 p3 y)
!,⊢wkTm v p1 (p2 ⇒ p3) p (Λ y) =
   begin
   _ ≡⟨ ≡Λ (!,⊢wkTm (vs v) (p1 , p2) p3 p y) ⟩
   _ ≡⟨ ≡Λ (≡wkTm _ (!,⊢-mod-proof _ _ _ _ y)) ⟩
   _ ∎
!,⊢wkTm v p1 p2 p (y · y') = !,⊢wkTm v p1 (≡τrefl ⇒ p2) p y ≡· !,⊢wkTm v p1 (≡τrefl) p y'

!,⊢wkTmvz : ∀ {Γ Δ τ σ a b} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (p3 : a ≡τ b)
          → (t : Γ ⊢ τ) 
          → ! (p1 , p3) , p2 >⊢ wkTm vz t ≡ wkTm vz (! p1 , p2 >⊢ t)
!,⊢wkTmvz {a = a} p1 p2 p3 t with !,⊢wkTm vz (p1 , p3) p2 p3 t
!,⊢wkTmvz {a = a} p1 p2 p3 t | r with ≡τ-≡ (≡τtrans (≡τsym p3) p3)
!,⊢wkTmvz p1 p2 p3 t | r | refl = r 

wkTmExc : ∀ {Γ σ τ ρ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → (t : Γ - x - y ⊢ ρ) 
       → wkTm (wkv x y) (wkTm (rem x y) (! Γ-- x y , ≡τrefl >⊢ t)) ≡ wkTm x (wkTm y t)
wkTmExc x y (var v) = ≡var (wkvExc x y v)
wkTmExc x y (Λ t) = ≡Λ (wkTmExc (vs x) (vs y) t)
wkTmExc x y (_·_ t₁ t₂) = wkTmExc x y t₁ ≡· wkTmExc x y t₂

wkTmExcvz : ∀ {Γ σ τ ρ} → (x : Γ ∋ σ) -> (t : Γ - x ⊢ ρ)
          → wkTm {τ} vz (wkTm x t) ≡ wkTm (vs x) (wkTm vz t)
wkTmExcvz x t =
  begin
  _ ≡⟨ ≡weaken (≡wkTm x (sym (!,⊢-id ≡Γrefl ≡τrefl t))) ⟩
  _ ≡⟨ wkTmExc (vs x) vz t ⟩
  _ ∎

wkTm-inj : ∀ {Γ σ τ} {v : Γ ∋ σ} → (e e' : Γ - v ⊢ τ) → wkTm v e ≡ wkTm v e' → e ≡ e'
wkTm-inj (var y) (var y') p = ≡var (wkv-inj _ y y' (var-inj p))
wkTm-inj (var y) (Λ y') ()
wkTm-inj (var y) (y' · y0) ()
wkTm-inj (Λ y) (var y') ()
wkTm-inj (Λ y) (Λ y') p = ≡Λ (wkTm-inj y y' (Λ-inj p))
wkTm-inj (Λ y) (y' · y0) ()
wkTm-inj (y · y') (var y0) ()
wkTm-inj (y · y') (Λ y0) ()
wkTm-inj (y · y') (y0 · y1) p with ·-inj-index p
wkTm-inj (y · y') (y0 · y1) p | refl = wkTm-inj y y0 (·-inj-left p) ≡· wkTm-inj y' y1 (·-inj-right p)
\end{code}
%endif