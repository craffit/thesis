%if False
\begin{code}

open import STLC public

module TTS.Judgement (A : ℕ) (R : Ty) 
  (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A) where

import TTS.Rules
open TTS.Rules A R rep public

module RuleJudgement (rules : Rules) where
  open import Util.PropositionalEquality

  open import TTS.Functor.Base
  open import TTS.Context.Base
\end{code}
%endif

\begin{code}
  
  data _∶_⊨_↝_ : (φ : Ftx) → (Φ : Functor) → ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)
               → ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R → Set where
       var     : ∀ {φ Φ} (v : φ ∋↝ Φ)
               → φ ∶ Φ ⊨ var (⟦ v ⟧∋ (C A)) ↝ var (⟦ v ⟧∋ R)
       app     : ∀ {φ Φ₁ Φ₂ e₁ e₁' e₂ e₂'} 
               → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ e₁ ↝ e₁' → φ ∶ Φ₁ ⊨ e₂ ↝ e₂' 
               → φ ∶ Φ₂ ⊨ (e₁ · e₂) ↝ (e₁' · e₂')
       lam     : ∀ {φ Φ₁ Φ₂ e e'} → (φ , Φ₁) ∶ Φ₂ ⊨ e ↝ e' → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ Λ e ↝ Λ e'
       i-rep   : ∀ {φ e e'} → φ ∶ K A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ (up rep · e')
       i-abs   : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ K A ⊨ e ↝ (up abs · e') 
       rule    : ∀ {φ Φ e e'} → Rule {Φ} e e' rules → φ ∶ Φ ⊨ up e ↝ up e'

  id-v : ∀ {Γ τ} → (v : Γ ∋ τ) → Γ ↑φ ∋↝ τ ↑Φ
  id-v vz = vz
  id-v (vs y) = vs (id-v y)

  id-v-eq : ∀ {Γ τ a} → (v : Γ ∋ τ) → ⟦ id-v v ⟧∋ a ≡ ! ↑φ-≡Γ , ↑Φ-≡τ >∋ v
  id-v-eq vz = sym (!,∋vz ↑φ-≡Γ _ _)
  id-v-eq (vs y) = ≡vs (id-v-eq y)

  ≡!_,_>↝_ : ∀ {φ Φ e e' f f'} → e ≡ e' → f ≡ f' → φ ∶ Φ ⊨ e ↝ f → φ ∶ Φ ⊨ e' ↝ f' 
  ≡! refl , refl >↝ v = v

  id↝ : ∀ {Γ τ} → (e : Γ ⊢ τ) 
      → Γ ↑φ ∶ τ ↑Φ ⊨ (! ↑φ-≡Γ , ↑Φ-≡τ >⊢ e) ↝ (! ↑φ-≡Γ , ↑Φ-≡τ >⊢ e)
  id↝ (var v)  = ≡! ≡var (id-v-eq v) , ≡var (id-v-eq v) >↝ var (id-v v)
  id↝ (Λ y)    = lam (id↝ y)
  id↝ (y · y') = ≡! !,⊢-split-· y y' ↑φ-≡Γ ↑Φ-≡τ ↑Φ-≡τ , !,⊢-split-· y y' ↑φ-≡Γ ↑Φ-≡τ ↑Φ-≡τ >↝ app (id↝ y) (id↝ y')


\end{code}
