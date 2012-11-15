\begin{code}

module Util.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning
open import Level

■ : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a
■ = refl

■' : ∀ {ℓ} {A : Set ℓ} → (a : A) → a ≡ a
■' _ = refl

\end{code}

