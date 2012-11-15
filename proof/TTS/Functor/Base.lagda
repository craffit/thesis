%if False
\begin{code}
module TTS.Functor.Base where

open import STLC
open import Data.Nat public

infixr 4 _⟶_
\end{code}
%endif

With the object language laid out, we move on to develop a representation for |(TTS(stlc))| in Agda. Essential to this type and transform system is the typing functor. The typing functor is defined as a straightforward inductive datatype as follows:

\begin{code}
data Functor : Set where
  Id    : Functor
  K     : (A : ℕ) → Functor
  _⟶_  : (Φ₁ Φ₂ : Functor) → Functor
\end{code}

The |Id| constructor represents the hole in the functor and the |K| constructor represents a constant type from the object language. Function space is represented by |_⟶_|. The functor data type is essentially a universe type for functors. We can interpret this universe as types in the object language, using the following interpretation function:

\begin{code} 
⟦_⟧Φ_ : Functor → Ty → Ty
⟦ Id       ⟧Φ n = n
⟦ K a      ⟧Φ n = C a
⟦ Φ₁ ⟶ Φ₂  ⟧Φ n = ⟦ Φ₁ ⟧Φ n ⇒ ⟦ Φ₂ ⟧Φ n
\end{code}

The functor interpretation function takes a functor and a type to fill into the holes and constructs a type in the object language. Using this interpretation on the type level, we can also construct an accompanying term-level functor for the object language. 

\begin{code}
dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ (a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a
dimap Id         = Λ (Λ (v 0))
dimap (K n)      = Λ (Λ id)
dimap (Φ₁ ⟶ Φ₂) = Λ (Λ (Λ (up (dimap Φ₂) · v 2 · v 1 ∘ v 0 ∘ up (dimap Φ₁) · v 1 · v 2)))
\end{code}

\begin{code}
_↑Φ : Ty → Functor
(C y) ↑Φ = K y
(y ⇒ y') ↑Φ = y ↑Φ ⟶ y' ↑Φ

↑Φ-≡τ : ∀ {a τ} → τ ≡τ ⟦ τ ↑Φ ⟧Φ a
↑Φ-≡τ {a} {C y} = C y
↑Φ-≡τ {a} {y ⇒ y'} = ↑Φ-≡τ ⇒ ↑Φ-≡τ
\end{code}

\begin{code}
data _↓Φ : Functor → Set where
  C    : ∀ n → (K n) ↓Φ
  _⟶_ : ∀ {Φ₁ Φ₂} → Φ₁ ↓Φ → Φ₂ ↓Φ → (Φ₁ ⟶ Φ₂) ↓Φ

_↓τ : ∀ {Φ} → Φ ↓Φ → Ty
(C n) ↓τ     = C n
(y ⟶ y') ↓τ = y ↓τ ⇒ y' ↓τ

↓Φ-≡τ : ∀ {a Φ} {v : Φ ↓Φ} → v ↓τ ≡τ ⟦ Φ ⟧Φ a
↓Φ-≡τ {a} {Id} {()}
↓Φ-≡τ {a} {K .y} {C y} = C y
↓Φ-≡τ {a} {Φ₁ ⟶ Φ₂} {v ⟶ v'} = ↓Φ-≡τ ⇒ ↓Φ-≡τ

\end{code}
%endif