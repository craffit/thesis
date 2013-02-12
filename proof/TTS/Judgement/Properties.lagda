%if False
\begin{code}

open import STLC public
open import TTS.Rules.Base

open import Util.PropositionalEquality

open import TTS.Functor.Base
open import TTS.Context.Base

module TTS.Judgement.Properties
       (A : ℕ) (R : Ty) 
       (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A) 
       (rules : Rules A R)
         where

import TTS.Judgement.Base
open TTS.Judgement.Base A R rep abs rules

id-v : ∀ {Γ τ} → (v : Γ ∋ τ) → Γ ↑φ ∋φ τ ↑Φ
id-v vz = vz
id-v (vs y) = vs (id-v y)

id-v-eq : ∀ {Γ τ a} → (v : Γ ∋ τ) → ⟦ id-v v ⟧∋ a ≡ ! ↑φ-≡Γ , ↑Φ-≡τ >∋ v
id-v-eq vz = sym (!,∋vz ↑φ-≡Γ _ _)
id-v-eq (vs y) = ≡vs (id-v-eq y)

≡!_,_>↝_ : ∀ {φ Φ e e' f f'} → e ≡ e' → f ≡ f' → φ ∶ Φ ⊨ e ↝ f → φ ∶ Φ ⊨ e' ↝ f' 
≡! refl , refl >↝ v = v

id↝  : ∀ {Γ τ} → (e : Γ ⊢ τ) 
     → Γ ↑φ ∶ τ ↑Φ ⊨ ! ↑φ-≡Γ , ↑Φ-≡τ >⊢ e ↝ ! ↑φ-≡Γ , ↑Φ-≡τ >⊢ e
id↝ (var v)  = ≡! ≡var (id-v-eq v) , ≡var (id-v-eq v) >↝ var (id-v v)
id↝ (Λ y)    = lam (id↝ y)
id↝ (y · y') = ≡! !,⊢-split-· y y' ↑φ-≡Γ ↑Φ-≡τ ↑Φ-≡τ , !,⊢-split-· y y' ↑φ-≡Γ ↑Φ-≡τ ↑Φ-≡τ >↝ app (id↝ y) (id↝ y')

\end{code}

%endif

%if False
\begin{code}
{-
\end{code}
%endif

\begin{code}
id↝  : ∀ {Γ τ} → (e : Γ ⊢ τ) → Γ ↑φ ∶ τ ↑Φ ⊨ e ↝ e
\end{code}

%if False
\begin{code}
-}
\end{code}
%endif