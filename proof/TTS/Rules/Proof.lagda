%if False
\begin{code}

open import STLC

module TTS.Rules.Proof  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

open import TTS.Rules.Base

import TTS.Relation.Base
open TTS.Relation.Base A R rep

open import TTS.Functor.Base
open import TTS.Context.Base
open import Util.PropositionalEquality
\end{code}
%endif

\begin{code}
data RuleProofs : Rules A R → Set where
  ε      :  RuleProofs ε
  proof  :  ∀ {rs Φ} → RuleProofs rs → (e : ε ⊢ ⟦ Φ ⟧Φ C A) 
            → (e' : ε ⊢ ⟦ Φ ⟧Φ R) → (r : rel {ε} {Φ} e e' ε ε)
            → RuleProofs (replace {A} {R} {Φ} rs e e')
\end{code}

%if False
\begin{code}
getProof  : ∀ {rs Φ} {e : ε ⊢ ⟦ Φ ⟧Φ C A} {e' : ε ⊢ ⟦ Φ ⟧Φ R} 
          → Rule {Φ} e e' rs → RuleProofs rs → rel {ε} {Φ} e e' ε ε
getProof {.(replace rs e e')} {Φ} {e} {e'} (rule rs) (proof y .e .e' r) = r
getProof (skip {rs} {Φ'} {f} {f'} r) (proof y .f .f' r') = getProof r y


\end{code}
%endif