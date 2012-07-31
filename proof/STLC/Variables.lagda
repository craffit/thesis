%if False
\begin{code}

module STLC.Variables where

open import STLC.Base
open import Relation.Nullary.Decidable

open import Data.Nat
open import Data.Fin hiding (_-_)

\end{code}
%endif

For convenience we define the function |v| which injects a natural number into a de Bruijn indiced variable. This only works if the type of the variable can be inferred from the context and the size of the context is known. 

\begin{code}

-- The size of a type context
size : Con → ℕ
size ε = zero
size (y , y') = suc (size y)

-- Retrieve the type of a type context using the Fin type. The Fin type is bounded by the size of the context
ind : (Γ : Con) → Fin (size Γ) → Ty
ind ε ()
ind (y , y') zero     = y'
ind (y , y') (suc i)  = ind y i

-- Turn a Fin-based variable index into a normal variable reference.
i' : ∀ {Γ} → (i : Fin (size Γ)) → Γ ∋ ind Γ i
i' {ε} ()
i' {y , y'} zero     = vz
i' {y , y'} (suc i)  = vs (i' i)

-- Construct a variable reference from a natural number and an inferred context
i : ∀ m {Γ} {m<n : True (suc m ≤? size Γ)} → Γ ∋ ind Γ (#_ m {size Γ} {m<n})
i v = i' (# v)

-- Construct a variable term from a natural number and an inferred context
v : ∀ m {Γ} {m<n : True (suc m ≤? size Γ)} → Γ ⊢ ind Γ (#_ m {size Γ} {m<n})
v x = var (i x)

\end{code}