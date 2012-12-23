%if False
\begin{code}
open import STLC

open import TTS.Functor.Base
open import TTS.Context.Base
open import Util.PropositionalEquality

module TTS.Relation.Env  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

import TTS.Relation.Base
open TTS.Relation.Base A R rep

\end{code}
%endif

\begin{code}
data Rel↓ : (φ : Ftx)  → (⟦ φ ⟧φ C A ↓) → (⟦ φ ⟧φ R ↓) → Set where
  ε    :  Rel↓ ε ε ε
  cls  :  ∀ {φ Φ} {e : ⟦ φ ⟧φ C A ⊢ ⟦ Φ ⟧Φ C A} {e' : ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R}
          → {s : ⟦ φ ⟧φ C A ↓} → {s' : ⟦ φ ⟧φ R ↓} → Rel↓ φ s s' 
          → (w : rel {φ} {Φ} e e' s s') → Rel↓ (φ , Φ) (cls s e) (cls s' e')
\end{code}

