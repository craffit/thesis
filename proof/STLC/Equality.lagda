%if False
\begin{code}

open import STLC.Base
open import STLC.SSubst
open import STLC.Up

\end{code}
%endif

\begin{code}
infix 1 _βη-≡_

data _βη-≡_ {Γ : Con} : {σ : Ty} → Tm Γ σ → Tm Γ σ → Set where
  brefl : forall {σ} → {t : Tm Γ σ} → t βη-≡ t
  bsym : forall {σ} → {t₁ t₂ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  btrans : forall {σ} → {t₁ t₂ t₃ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  congΛ : forall {σ τ} → {t₁ t₂ : Tm (Γ , σ) τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  congApp : forall {σ τ} → {t₁ t₂ : Tm Γ (σ ⇒ τ)} → {u₁ u₂ : Tm Γ σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₁ βη-≡ app t₂ u₂
  beta : forall {σ τ} → {t : Tm (Γ , σ) τ} → {u : Tm Γ σ} → app (Λ t) u βη-≡ (t / sub vz u)
  eta : forall {σ τ} → {t : Tm Γ (σ ⇒ τ)} → Λ (app (wkTm vz t) (var vz)) βη-≡ t

\end{code}
            
%if False
\begin{code}
open import Relation.Binary hiding (_⇒_)

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
-- open ≡-Reasoning

βηsetoid : {Γ : Con} {σ : Ty} → Setoid _ _
βηsetoid {Γ} {σ} = 
  record { Carrier = Tm Γ σ 
         ; _≈_ = _βη-≡_
         ; isEquivalence = 
              record { refl  = brefl
                     ; sym   = bsym
                     ; trans = btrans
                     }                              
         }

-- Congruences of βη-≡

equiv : forall {Γ σ} → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
equiv refl = brefl


congSubstVar : forall {σ Γ τ} → (v : Var Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl


congWkTm : forall {Γ σ τ} → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm _ brefl = brefl
congWkTm x (bsym p) = bsym (congWkTm x p)
congWkTm x (btrans p₁ p₂) = btrans (congWkTm x p₁) (congWkTm x p₂)
congWkTm x (congΛ p) = congΛ (congWkTm (vs x) p)
congWkTm x (congApp p₁ p₂) = congApp (congWkTm x p₁) (congWkTm x p₂)
congWkTm x {app (Λ t) u} beta = btrans beta 
  (equiv 
    ( ≡begin
    _ ≡⟨ sym (subst/ vz (wkTm (vs x) t) (wkTm x u)) ⟩
    _ ≡⟨ sym (wkTmSubstExc (vs x) t vz u) ⟩
    _ ≡⟨ cong (\p → wkTm x p) (subst/ vz t u) ⟩    
    _ ≡∎
    )
  )
congWkTm x {._} {t} eta = btrans (congΛ (congApp (equiv (wkTmExc vz x t)) brefl)) eta


congSubst : forall {σ Γ τ} → (t : Tm Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → subst t x u₁ βη-≡ subst t x u₂
congSubst (var v) x p = congSubstVar v x p
congSubst (Λ t) x p = congΛ (congSubst t (vs x) (congWkTm vz p))
congSubst (app t₁ t₂) x p = congApp (congSubst t₁ x p) (congSubst t₂ x p)

congUp : forall {Γ τ} → {t t' : Tm ε τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
congUp {ε} t0 = t0
congUp {y , y'} {_} {t} {t'} t0 = congWkTm vz (congUp {y} t0)

cong/ : ∀ {Γ Δ τ} → {t t' : Tm Γ τ} → t βη-≡ t' → (s : Γ => Δ) → (t / s) βη-≡ (t' / s)
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
       _ ⟷⟨ equiv (cong (λ p → p / ss s (u / s)) (sym (ι/ t))) ⟩
       _ ⟷⟨ bsym (equiv (comm-/ vz t vz u ι s)) ⟩
       _ ∎
cong/ (eta {_} {_} {t}) s =    
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ congΛ (congApp (equiv (wkSI/ vz vz t s)) brefl) ⟩
       _ ⟷⟨ eta ⟩
       _ ∎
-- Proofs that involve with
{-
substSame : forall {Γ σ} → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → eq x x ≡ same → u βη-≡ substVar x x u
substSame x u p with eq x x
substSame x u refl | .same = brefl


substDiff : forall {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (u : Tm (Γ - x) σ) → eq x (wkv x y) ≡ diff x y → var y βη-≡ substVar (wkv x y) x u
substDiff x y u p with eq x (wkv x y)
substDiff x y u refl | .(diff x y) = brefl 
-}
\end{code}
%endif