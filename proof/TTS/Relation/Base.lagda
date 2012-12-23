%if False
\begin{code}
open import STLC

open import TTS.Functor.Base
open import TTS.Context.Base
open import Util.PropositionalEquality

\end{code}
%endif


\begin{code}
module TTS.Relation.Base  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

rel : ∀ {φ Φ} → (e : ⟦ φ ⟧φ C A ⊢ ⟦ Φ ⟧Φ C A) → (e' : ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R)
    → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) → Set
rel {φ} {Id}        e e' s s' = up rep · close e s βη-≡ close e' s' 
rel {φ} {C n}       e e' s s' = close e s βη-≡ close e' s' 
rel {φ} {Φ₁ ⟶ Φ₂}   e e' s s' = ∀ a a'  → rel {φ} {Φ₁} a a' s s' 
                                        → rel {φ} {Φ₂} (e · a) (e' · a') s s'
\end{code}

%if False
\begin{code}

≡rel : ∀ {φ Φ} {e e' : ⟦ φ ⟧φ C A ⊢ ⟦ Φ ⟧Φ C A} {f f' : ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R}
     {s s' : ⟦ φ ⟧φ C A ↓} {t t' : ⟦ φ ⟧φ R ↓} → e ≡ e' → f ≡ f' → s ≡ s'
     → t ≡ t' → rel {φ} {Φ} e f s t → rel {φ} {Φ} e' f' s' t'
≡rel refl refl refl refl v = v
                                         
\end{code}
%endif