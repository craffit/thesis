%if False
\begin{code}
module STLC.Term.Inject where

open import STLC.Term.Base
open import Relation.Nullary.Decidable
open import Data.Fin hiding (_-_)

\end{code}
%endif

\begin{code}
v :  (m : ℕ) → {Γ : Con} → {m<n : True (suc m ≤? size Γ)} 
     → Γ ⊢ ind Γ (#_ m {size Γ} {m<n})
v x = var (i x)
\end{code}
