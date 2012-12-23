\begin{code}
module STLC.Termination where

open import Data.Product
open import STLC.Term

infixl 7 _⟶_
infix 1 _β⟶_
--infix 1 _β⟶*_
infix 1 _*⟵β_

  
mutual
  data Nf {Γ : Con} : {τ : Ty} → Γ ⊢ τ → Set where
    Λ   : ∀ {σ τ} {t : Γ , σ ⊢ τ} → Nf t → Nf (Λ t)
    _·_ : ∀ {σ τ} {t : Γ ⊢ σ} → (v : Γ ∋ σ ⇒ τ) → Nf t → Nf (var v · t)
    var : ∀ {σ} → (v : Γ ∋ σ) → Nf (var v)

data _β⟶_ {Γ : Con} : {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → Set where
  %Λ_   : ∀ {σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → t₁ β⟶ t₂ → Λ t₁ β⟶ Λ t₂
  appl  : ∀ {σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u : Γ ⊢ σ} 
        → t₁ β⟶ t₂ → t₁ · u β⟶ t₂ · u
  appr  : ∀ {σ τ} → {t : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} 
        → u₁ β⟶ u₂ → t · u₁ β⟶ t · u₂
  beta  : ∀ {σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u β⟶ t / sub vz u

data _*⟵β_ {Γ : Con} {σ : Ty} (r : Γ ⊢ σ) : Γ ⊢ σ → Set where
  nf    : Nf r → r *⟵β r
  _⟶_  : ∀ {t t'} → t β⟶ t' → r *⟵β t' → r *⟵β t

hasnf : ∀ {Γ τ} → (e : Γ ⊢ τ) → Set
hasnf {Γ} {τ} e = Σ (Γ ⊢ τ) (λ r → r *⟵β e)   

subnf : ∀ {Γ σ τ} → (e : Γ , σ ⊢ τ) → (e' : Γ ⊢ σ)
          → hasnf e → hasnf e' → hasnf (e / sub vz e')
subnf (var vz) e' (.(var vz) , nf y') (nfe' , de') = nfe' , de'
subnf (var (vs y)) e' (.(var (vs y)) , nf y') (nfe' , de') = {!!}
subnf (var y) e' (nfe , () ⟶ y0) (nfe' , de')
subnf (Λ y) e' (nfe , de) (nfe' , de')    = {!!}
subnf (y · y') e' (nfe , de) (nfe' , de') = {!nfe!}
{-
red : ∀ {Γ τ} → (e : Γ ⊢ τ) → Σ (Γ ⊢ τ) (\r → r *⟵β e)
red (var y) = {!!}
red (Λ y) = {!!}
red (var y · y') = {!!}
red (Λ y · y') = {!!}
red (y · y' · y0) = {!!}
-}
{-
    ne : ∀ {τ} {t : Γ ⊢ τ} → Ne t → Nf t

  data Ne {Γ : Con}
-}

rel : ∀ {Γ τ} → Γ ⊢ τ → Set
rel {Γ} {C y}    e = hasnf e
rel {Γ} {y ⇒ y'} e = ∀ e' → hasnf e' → rel e' → rel (e · e')

rel-red : ∀ {Γ τ} → (e e' : Γ ⊢ τ) → e β⟶ e' → rel e' → rel e
rel-red {Γ} {C y} e e' r (n , d) = n , (r ⟶ d)
rel-red {Γ} {y ⇒ y'} e e' r re   = λ a nfa ra → rel-red (e · a) (e' · a) (appl r) (re a nfa ra) 

mutual
  rel-sub : ∀ {Γ σ τ} → (e : Γ , σ ⊢ τ) → (e' : Γ ⊢ σ)
          → rel e → rel e' → rel (e / sub vz e')
  rel-sub {Γ} {σ} {C y} e e' re re' = {!!}
  rel-sub {Γ} {σ} {y ⇒ y'} e e' re re' = λ a nfa ra → {!re (wkTm vz a) ? !}

  rel-wk : ∀ {Γ σ τ} → (e : Γ ⊢ τ) → rel e → rel (wkTm {σ} vz e)
  rel-wk e r = {!!}

  rel-sub' : ∀ {Γ σ τ} → (e : Γ , σ ⊢ τ) → (e' : Γ ⊢ σ)
          → rel e' → rel (e / sub vz e') → rel e
  rel-sub' {Γ} {σ} {C y} e e' re rs = {!!}
  rel-sub' {Γ} {σ} {y ⇒ y'} e e' re rs = λ a nfa ra → {!!}

data Rel=> {Γ : Con} : ∀ {Δ} → Δ => Γ → Set where
  sz : Rel=> sz
  ss : ∀ {Δ σ} {s : Δ => Γ} {t : Γ ⊢ σ} → Rel=> s → rel t → Rel=> (ss s t)

fund : ∀ {Γ τ} → (e : Γ ⊢ τ) → rel e
fund {Γ} {C y} (var y') = var y' , nf (var y')
fund {Γ} {y ⇒ y'} (var y0) = {!!}
fund (Λ y) = λ e enf re → rel-red (Λ y · e) (y / ss I e) beta {!!}
fund (y · y') = {!!}

\end{code}