\begin{code}

module Util.Invertible where

open import Level
open import Util.PropositionalEquality

data Undo {ℓ ℓ₂ : Level} {A : Set ℓ} {B : Set ℓ₂} (f : A → B) : B → Set (ℓ ⊔ ℓ₂) where
  Pack : (v : A) → Undo f (f v)

undo : ∀ {ℓ ℓ₂} {A : Set ℓ} {B : Set ℓ₂} {f : A → B} {v : B} → Undo f v → A
undo (Pack v) = v 

undo-id : ∀ {ℓ ℓ₂} {A : Set ℓ} {B : Set ℓ₂} {f : A → B} {v : A}
        → (∀ {a b} → f a ≡ f b → a ≡ b) → (u : Undo f (f v)) → undo u ≡ v
undo-id {f = f} {v = v} inj u with f v | inspect f v
undo-id {f = f} {v = v} inj (Pack v') | .(f v') | [ eq ] = sym (inj eq)

\end{code}