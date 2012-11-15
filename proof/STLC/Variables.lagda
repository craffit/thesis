%if False
\begin{code}

module STLC.Variables where

open import STLC.Base

open import Relation.Nullary.Decidable

open import Data.Nat
open import Data.Fin hiding (_-_)

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

\end{code}
%endif

\paragraph{Injecting variables} For convenience we define the function |v| which injects a natural number into a de Bruijn indiced variable. |v| is defined as follows:

\begin{code}
v : (m : ℕ) → {Γ : Con} → {m<n : True (suc m ≤? size Γ)} → Γ ⊢ ind Γ (#_ m {size Γ} {m<n})
v x = var (i x)
\end{code}

In the type of v, the function |ind| takes a context and a finite number with equal size and returns the type at the position of the given number. The finite number is constructed using the function |#_|, which injects a natural number into a finite number which is bounded by |size Γ|. Only natural numbers which are smaller that the upper bound can be injected into a finite number. This is implicitly proven by the term |True (suc m ≤? size Γ)|. This expression will resolve to the type unit when the condition holds and will resolve to bottom if not. Unit can be implicitly constructed and will thus pass the type checker. Bottom will fail to type check, because it has no value representing it and thus cannot be inferred or passed. The function |i| takes care of constructing the STLC term for the constructed types.
