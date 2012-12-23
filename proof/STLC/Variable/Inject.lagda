%if False
\begin{code}

module STLC.Variable.Inject where

open import STLC.Variable.Base

open import Relation.Nullary.Decidable

open import Data.Nat
open import Data.Fin hiding (_-_)
\end{code}
%endif

\begin{code}
size : Con → ℕ
size ε         = zero
size (y , y')  = suc (size y)

ind : (Γ : Con) → Fin (size Γ) → Ty
ind ε ()
ind (y , y') zero     = y'
ind (y , y') (suc i)  = ind y i

i' : ∀ {Γ} → (i : Fin (size Γ)) → Γ ∋ ind Γ i
i' {ε} ()
i' {y , y'} zero     = vz
i' {y , y'} (suc i)  = vs (i' i)

i : ∀ m {Γ} {m<n : True (suc m ≤? size Γ)} → Γ ∋ ind Γ (#_ m {size Γ} {m<n})
i v = i' (# v)

\end{code}
