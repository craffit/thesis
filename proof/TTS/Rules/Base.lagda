%if False
\begin{code}

module TTS.Rules.Base where

open import STLC
open import TTS.Functor.Base
open import TTS.Context.Base

\end{code}
%endif

\begin{code}
data Rules (A : ℕ) (R : Ty) : Set where
  ε        : Rules A R
  replace  : ∀ {Φ} → (r : Rules A R) → (e : ε ⊢ ⟦ Φ ⟧Φ C A) 
           → (e' : ε ⊢ ⟦ Φ ⟧Φ R) → Rules A R

data Rule {Φ A R} (e : ε ⊢ ⟦ Φ ⟧Φ C A) (e' : ε ⊢ ⟦ Φ ⟧Φ R) : Rules A R → Set where
  rule : ∀ rs → Rule e e' (replace {A} {R} {Φ} rs e e')
  skip : ∀ {rs Φ' f f'}  → (r : Rule {Φ} e e' rs) 
                         → Rule e e' (replace {A} {R} {Φ'} rs f f')

\end{code}