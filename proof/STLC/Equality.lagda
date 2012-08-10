%if False
\begin{code}
module STLC.Equality where

open import STLC.Base
open import STLC.SSubst
open import STLC.Up

infixl 7 _⟷_
infix 1 _βη-≡_
infixl 3 _%·_
\end{code}

%endif

We also need a relation which relates the semantics of the terms in the STLC object language. We use $\beta\eta$-equivalence relation as presented in Keller and Altenkirch~\cite{keller10}. 

\begin{code}

data _βη-≡_ {Γ : Con} : {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → Set where
  □     : ∀ {σ} → {t : Γ ⊢ σ} → t βη-≡ t
  bsym  : ∀ {σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  _⟷_   : ∀ {σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  %Λ_   : ∀ {σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  _%·_  : ∀ {σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} 
        → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ →  t₁ · u₁ βη-≡ t₂ · u₂
  beta  : ∀ {σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u βη-≡ t / sub vz u
  eta   : ∀ {σ τ} → {t : Γ ⊢ σ ⇒ τ} → Λ (wkTm vz t · var vz) βη-≡ t

\end{code}

This relation also gives rise to a setoid, which makes it possible to do equational reasoning with STLC terms.
            
%if False
\begin{code}
brefl : ∀ {Γ σ} {t : Γ ⊢ σ} → t βη-≡ t
brefl = □

btrans : ∀ {Γ σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
btrans = _⟷_

congΛ : ∀ {Γ σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
congΛ = %Λ_

congApp : ∀ {Γ σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ}
                → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ →  t₁ · u₁ βη-≡ t₂ · u₂
congApp = _%·_

 
infix 1 _βη-=>_

data _βη-=>_ {Δ : Con} : {Γ : Con} → Γ => Δ → Γ => Δ → Set where
  sz : sz βη-=> sz
  ss : ∀ {Γ τ} {s1 s2 : Γ => Δ} {t1 t2 : Δ ⊢ τ} 
     → s1 βη-=> s2 → t1 βη-≡ t2 → ss s1 t1 βη-=> ss s2 t2

=>refl : ∀ {Γ Δ} {s : Γ => Δ} → s βη-=> s
=>refl {.ε} {Δ} {sz} = sz
=>refl {Γ , τ} {Δ} {ss y y'} = ss (=>refl {Γ} {Δ} {y}) brefl

=>sym : ∀ {Γ Δ} {s s' : Γ => Δ} → s βη-=> s' → s' βη-=> s
=>sym sz = sz
=>sym (ss y y') = ss (=>sym y) (bsym y')

=>trans : ∀ {Γ Δ} {s s' s'' : Γ => Δ} → s βη-=> s' → s' βη-=> s'' → s βη-=> s''
=>trans sz p2 = p2
=>trans (ss y y') (ss y0 y1) = ss (=>trans y y0) (btrans y' y1)

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

βη=>setoid : {Γ Δ : Con} → Setoid _ _
βη=>setoid {Γ} {Δ} = 
  record { Carrier = Γ => Δ 
         ; _≈_ = _βη-=>_
         ; isEquivalence = 
              record { refl  = =>refl
                     ; sym   = =>sym
                     ; trans = =>trans
                     }                              
         }

-- Congruences of βη-≡

equiv : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
equiv refl = brefl

=>≡ : ∀ {Γ Δ} → {t1 t2 : Γ => Δ} → t1 ≡ t2 → t1 βη-=> t2
=>≡ refl = =>refl

congSubstVar : ∀ {σ Γ τ} → (v : Γ ∋ τ) → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl


congWkTm : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm _ □ = □
congWkTm x (bsym p) = bsym (congWkTm x p)
congWkTm x (p₁ ⟷ p₂) = btrans (congWkTm x p₁) (congWkTm x p₂)
congWkTm x (%Λ p) = congΛ (congWkTm (vs x) p)
congWkTm x (p₁ %· p₂) = congApp (congWkTm x p₁) (congWkTm x p₂)
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
cong/ □ s = □
cong/ (bsym y) s = bsym (cong/ y s)
cong/ (y ⟷ y') s = btrans (cong/ y s) (cong/ y' s)
cong/ (%Λ y) s = congΛ (cong/ y (ss (wkS vz s) (var vz)))
cong/ (y %· y') s = congApp (cong/ y s) (cong/ y' s)
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

cong-lookup-s : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (y : Γ ∋ τ) → lookup y s βη-≡ lookup y s'
cong-lookup-s {ε} sz ()
cong-lookup-s {y , .τ} {Δ} {τ} (ss y0 y1) vz = y1
cong-lookup-s {y , y'} (ss y0 y1) (vs y2) = cong-lookup-s y0 y2

cong-extS : ∀ {Γ Δ τ} {t t' : Δ ⊢ τ} → (v : Γ ∋ τ) → {s s' : Γ - v => Δ} → s βη-=> s' → t βη-≡ t' → extS v t s βη-=> extS v t' s'
cong-extS vz s0 t0 = ss s0 t0
cong-extS (vs y) (ss y' y0) t0 = ss (cong-extS y y' t0) y0

cong-wkS : ∀ {Γ Δ τ}  → (v : Δ ∋ τ) → {s s' : Γ => Δ - v} → s βη-=> s' → wkS v s βη-=> wkS v s'
cong-wkS v sz = sz
cong-wkS v (ss y y') = ss (cong-wkS v y) (congWkTm v y')

cong/s : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (t : Γ ⊢ τ) → t / s βη-≡ t / s'
cong/s s0 (var y) = cong-lookup-s s0 y
cong/s s0 (Λ y) = congΛ (cong/s (cong-extS vz (cong-wkS vz s0) brefl) y)
cong/s s0 (y · y') = congApp (cong/s s0 y) (cong/s s0 y')

congUp : ∀ {Γ τ} → {t t' : ε ⊢ τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
congUp {ε} t0 = t0
congUp {y , y'} {_} {t} {t'} t0 = congWkTm vz (congUp {y} t0)

!_β>₁_ : ∀ {Γ Δ τ} {t t' : Γ ⊢ τ} → (p : Γ ≡ Δ) → t βη-≡ t' → ! p >₁ t βη-≡ ! p >₁ t'
!_β>₁_ refl t0 = t0

!_β>τ_ : ∀ {Γ τ σ} {t t' : Γ ⊢ τ} → (p : τ ≡ σ) → t βη-≡ t' → ! p >τ t βη-≡ ! p >τ t'
!_β>τ_ refl t0 = t0

!β· : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t₁ : Γ ⊢ (σ ⇒ τ)) → (t₂ : Γ ⊢ σ) → ! p >₁ (t₁ · t₂) βη-≡ (! p >₁ t₁) · (! p >₁ t₂)
!β· refl _ _ = brefl

!_β>₂_ : ∀ {Γ Δ Δ'} {s s' : Γ => Δ} → (p : Δ ≡ Δ') → s βη-=> s' → ! p >₂ s βη-=> ! p >₂ s'
!_β>₂_ refl t0 = t0

\end{code}
%endif