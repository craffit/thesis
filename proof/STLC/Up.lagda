%if False
\begin{code}
module STLC.Up where

open import STLC.Base
open import STLC.SSubst

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
open ≡-Reasoning
\end{code}

%endif

\begin{code}

up : ∀ {Γ τ} → ε ⊢ τ → Γ ⊢ τ
up {ε} t = t
up {y , y'} t = weaken (up {y} t)

\end{code}

%if False
\begin{code}
commWkUp : ∀ {Γ τ σ} → (x : _∋_ Γ σ) → (t : _⊢_ ε τ) → up {Γ} t ≡ wkTm x (up {Γ - x} t)
commWkUp {ε} () t
commWkUp {y , σ} vz t       = refl
commWkUp {y , y'} (vs y0) t =
     begin
       wkTm vz (up t)
     ≡⟨ cong (λ i → wkTm vz i) (commWkUp y0 t) ⟩
       _
     ≡⟨ wkTmExc (vs y0) vz (up t) ⟩
       wkTm (vs y0) (wkTm vz (up t))
     ∎

up-· : ∀ {Δ τ σ} → (f : _⊢_ ε (σ ⇒ τ)) → (a : _⊢_ ε σ) → _·_ (up f) (up a) ≡ up {Δ} (_·_ f a)
up-· {ε} f a = refl
up-· {y , y'} f a = cong (\v → wkTm vz v) (up-· f a)

subst-up : ∀ {Γ} {τ σ} → (t : _⊢_ ε τ) → (v : _∋_ Γ σ) → (u : _⊢_ (Γ - v) σ) → subst (up {Γ} t) v u ≡ up t
subst-up {Γ} t v u =
     begin
       subst (up t) v u
     ≡⟨ cong (λ i → subst i v u) (commWkUp v t) ⟩
       subst (wkTm v (up t)) v u
     ≡⟨ weakSubst v (up t) u ⟩
       up t
     ∎

up-/sz : ∀ {Γ τ} → (t : _⊢_ ε τ) → up {Γ} t ≡ t / sz
up-/sz (var ())
up-/sz {ε} (Λ y) = cong Λ (sym (/ι y))
up-/sz {y , y'} (Λ y0) 
  = begin
  _ ≡⟨ cong (\p → wkTm vz p) (up-/sz {y} (Λ y0)) ⟩
  _ ≡⟨ cong Λ (sym (wkExtS/ vz (vs vz) y0 (ss sz (var vz)))) ⟩
  _ ≡⟨ cong Λ (wk-ext/ vz y0 (var (vs vz)) (ss sz (var vz))) ⟩
  _ ∎
up-/sz (y · y') 
  = begin
  _ ≡⟨ sym (up-· y y') ⟩
  _ ≡⟨ cong₂ _·_ (up-/sz y) (up-/sz y') ⟩
  _ ∎

up/ε : ∀ {Γ τ} → (t : _⊢_ ε τ) → (s : Γ => ε) → up t / s ≡ t
up/ε t sz = /ι t
up/ε t (ss y y') = begin
               _ ≡⟨ wk-ext/ vz (up t) y' y ⟩
               _ ≡⟨ up/ε t y ⟩
               _ ∎

up/ : ∀ {Γ Δ τ} → (t : _⊢_ ε τ) → (s : Γ => Δ) → up t / s ≡ up t
up/ {Γ} {ε} t s = up/ε t s
up/ {ε} {y , y'} t sz = begin
            _ ≡⟨ wk/ vz t sz ⟩
            _ ≡⟨ cong (\v → wkTm vz v) (up/ t sz) ⟩
            _ ∎
up/ {a , b} {y , y'} t (ss y0 y1) = begin
            _ ≡⟨ wk-ext/ vz (up t) y1 y0 ⟩
            _ ≡⟨ up/ t y0 ⟩
            _ ∎

sz/ : ∀ {Δ τ} → (t : _⊢_ ε τ) → t / (sz {Δ}) ≡ up t
sz/ {ε} t      = /ι t
sz/ {y , y'} t 
  = begin
  _ ≡⟨ wk/ vz t sz ⟩
  _ ≡⟨ cong (\p → wkTm vz p) (sz/ t) ⟩
  _ ∎
\end{code}
%endif