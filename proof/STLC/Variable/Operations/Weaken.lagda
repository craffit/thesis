\begin{code}

module STLC.Variable.Operations.Weaken where

open import STLC.Variable.Operations.Subtract
open import STLC.Variable.Base
open import STLC.Variable.Congruence
open import STLC.Context.Equality
open import Relation.Binary.PropositionalEquality

wkv : ∀ {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ∋ τ → Γ ∋ τ
wkv vz     y       = vs y
wkv (vs x) vz      = vz
wkv (vs x) (vs y)  = vs (wkv x y)

!,∋-wkv : ∀ {Γ Δ τ σ a b} → (v : Γ ∋ a) → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) 
       → (p3 : a ≡τ b) → (y : Γ - v ∋ τ) 
       → ! p1 , p2 >∋ wkv v y 
       ≡ wkv (! p1 , p3 >∋ v) (! (-≡Γ p1 p3 v) , p2 >∋ y)
!,∋-wkv vz (p1 , p2) p3 p y with  ≡τ-≡ (≡τtrans (≡τsym p2) p)
!,∋-wkv vz (p1 , p2) p3 p y | refl = refl
!,∋-wkv (vs y) (p1 , p2) p3 p vz with ≡τ-≡ p2 | ≡τ-≡ (≡τtrans (≡τsym p2) p3)
!,∋-wkv (vs y) (p1 , p2) p3 p vz | refl | refl with ≡τ-≡ (≡τtrans (≡τsym ≡τrefl) p3)
... | refl = refl
!,∋-wkv (vs y) (p1 , p2) p3 p (vs y') with ≡τ-≡ p2
!,∋-wkv (vs y) (p1 , p2) p3 p (vs y') | refl = cong vs (!,∋-wkv y p1 p3 p y')

≡wkv : ∀ {σ Γ τ} (x : Γ ∋ σ) → {v v' : Γ - x ∋ τ} → v ≡ v'
     → wkv x v ≡ wkv x v'
≡wkv x = cong (wkv x)

wkv-inj : ∀ {Γ σ τ} → (v : Γ ∋ σ) → (x x' : Γ - v ∋ τ) → wkv v x ≡ wkv v x' → x ≡ x'
wkv-inj vz vz vz p = refl
wkv-inj vz vz (vs j) ()
wkv-inj vz (vs i) vz ()
wkv-inj vz (vs .j) (vs j) refl = refl
wkv-inj (vs k) vz vz p = refl
wkv-inj (vs k) vz (vs j) ()
wkv-inj (vs k) (vs i) vz ()
wkv-inj (vs k) (vs i) (vs j) p = ≡vs (wkv-inj k i j (vs-inj p))
  

\end{code}