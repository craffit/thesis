%if False
\begin{code}
module STLC.Equality where

open import STLC.Base
open import STLC.SSubst
open import STLC.Up

\end{code}

%endif

We also need a relation which relates the semantics of the terms in the STLC object language. We use $\beta\eta$-equivalence relation as presented in Keller and Altenkirch~\cite{keller10}. 

\begin{code}
infix 1 _βη-≡_

data _βη-≡_ {Γ : Con} : {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → Set where
  brefl    : ∀ {σ} → {t : Γ ⊢ σ} → t βη-≡ t
  bsym     : ∀ {σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  btrans   : ∀ {σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  congΛ    : ∀ {σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  congApp  : ∀ {σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} 
           → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ →  t₁ · u₁ βη-≡ t₂ · u₂
  beta     : ∀ {σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u βη-≡ t / sub vz u
  eta      : ∀ {σ τ} → {t : Γ ⊢ σ ⇒ τ} → Λ (wkTm vz t · var vz) βη-≡ t

\end{code}

This relation also gives rise to a setoid, which makes it possible to do equational reasoning with STLC terms.
            
%if False
\begin{code}
open import Relation.Binary hiding (_⇒_)

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
import Relation.Binary.EqReasoning

βηsetoid : {Γ : Con} {σ : Ty} → Setoid _ _
βηsetoid {Γ} {σ} = 
  record { Carrier = Γ ⊢ σ 
         ; _≈_ = _βη-≡_
         ; isEquivalence = 
              record { refl  = brefl
                     ; sym   = bsym
                     ; trans = btrans
                     }                              
         }

-- Congruences of βη-≡

equiv : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
equiv refl = brefl


congSubstVar : ∀ {σ Γ τ} → (v : Γ ∋ τ) → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl


congWkTm : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm _ brefl = brefl
congWkTm x (bsym p) = bsym (congWkTm x p)
congWkTm x (btrans p₁ p₂) = btrans (congWkTm x p₁) (congWkTm x p₂)
congWkTm x (congΛ p) = congΛ (congWkTm (vs x) p)
congWkTm x (congApp p₁ p₂) = congApp (congWkTm x p₁) (congWkTm x p₂)
congWkTm x {Λ t · u} beta = 
  let open ≡-Reasoning
  in btrans beta 
  (equiv 
    ( begin
    _ ≡⟨ sym (subst/ vz (wkTm (vs x) t) (wkTm x u)) ⟩
    _ ≡⟨ sym (wkTmSubstExc (vs x) t vz u) ⟩
    _ ≡⟨ cong (\p → wkTm x p) (subst/ vz t u) ⟩    
    _ ∎
    )
  )
congWkTm x {._} {t} eta = btrans (congΛ (congApp (equiv (wkTmExc vz x t)) brefl)) eta


congSubst : ∀ {σ Γ τ} → (t : Γ ⊢ τ) → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ σ} → u₁ βη-≡ u₂ → subst t x u₁ βη-≡ subst t x u₂
congSubst (var v) x p = congSubstVar v x p
congSubst (Λ t) x p = congΛ (congSubst t (vs x) (congWkTm vz p))
congSubst (t₁ · t₂) x p = congApp (congSubst t₁ x p) (congSubst t₂ x p)

cong/ : ∀ {Γ Δ τ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → (s : Γ => Δ) → t / s βη-≡ t' / s
cong/ brefl s = brefl
cong/ (bsym y) s = bsym (cong/ y s)
cong/ (btrans y y') s = btrans (cong/ y s) (cong/ y' s)
cong/ (congΛ y) s = congΛ (cong/ y (ss (wkS vz s) (var vz)))
cong/ (congApp y y') s = congApp (cong/ y s) (cong/ y' s)
cong/ (beta {_} {_} {t} {u}) s =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ bsym (equiv (dist-sub vz t vz (u / s) s)) ⟩
       _ ⟷⟨ equiv (cong (λ p → p / ss s (u / s)) (sym (/ι t))) ⟩
       _ ⟷⟨ bsym (equiv (comm-/ vz t vz u ι s)) ⟩
       _ ∎
cong/ (eta {_} {_} {t}) s =    
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ congΛ (congApp (equiv (wkExtS/ vz vz t s)) brefl) ⟩
       _ ⟷⟨ eta ⟩
       _ ∎

congUp : ∀ {Γ τ} → {t t' : ε ⊢ τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
congUp {ε} t0 = t0
congUp {y , y'} {_} {t} {t'} t0 = congWkTm vz (congUp {y} t0)

\end{code}
%endif