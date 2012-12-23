%if False
\begin{code}
module TTS.Functor.Base where

open import STLC
open import Data.Nat public

infixr 5 _↑Φ
infixr 7 ⟦_⟧Φ_
infixr 4 _⟶_
\end{code}
%endif

With the object language layed out, it is now possible to formalize the basic constructs of |(TTS(stlc))|. Essential to the type and transform system is the typing functor. The typing functor is defined as a straightforward inductive datatype as follows:

\begin{code}
data Functor : Set where
  Id    : Functor
  C     : (A : ℕ) → Functor
  _⟶_   : (Φ₁ Φ₂ : Functor) → Functor
\end{code}

As expected, the functor datatype is the same as the stlc base type, with an extra constructor |Id| representing a hole in the type. Two functions establish the relation between functor types and normal types: The interpretation function |⟦_⟧Φ_| and the lifting function |_↑Φ|.

\begin{code} 
⟦_⟧Φ_ : Functor → Ty → Ty
⟦ Id       ⟧Φ τ = τ
⟦ C n      ⟧Φ τ = C n
⟦ Φ₁ ⟶ Φ₂  ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ

_↑Φ : Ty → Functor
C n      ↑Φ = C n
τ₁ ⇒ τ₂  ↑Φ = τ₁ ↑Φ ⟶ τ₂ ↑Φ
\end{code}

In the Agda world, the functor datatype can be seen as a universe, with |⟦_⟧Φ_| as universe interpretation onto the base types.
 
%if False
\begin{code}
↑Φ-≡τ : ∀ {a τ} → τ ≡τ ⟦ τ ↑Φ ⟧Φ a
↑Φ-≡τ {a} {C y} = C y
↑Φ-≡τ {a} {y ⇒ y'} = ↑Φ-≡τ ⇒ ↑Φ-≡τ

data _↓Φ : Functor → Set where
  C    : ∀ n → (C n) ↓Φ
  _⟶_ : ∀ {Φ₁ Φ₂} → Φ₁ ↓Φ → Φ₂ ↓Φ → (Φ₁ ⟶ Φ₂) ↓Φ

_↓τ : ∀ {Φ} → Φ ↓Φ → Ty
(C n) ↓τ     = C n
(y ⟶ y') ↓τ = y ↓τ ⇒ y' ↓τ

↓Φ-≡τ : ∀ {a Φ} {v : Φ ↓Φ} → v ↓τ ≡τ ⟦ Φ ⟧Φ a
↓Φ-≡τ {a} {Id} {()}
↓Φ-≡τ {a} {C .y} {C y} = C y
↓Φ-≡τ {a} {Φ₁ ⟶ Φ₂} {v ⟶ v'} = ↓Φ-≡τ ⇒ ↓Φ-≡τ

\end{code}
%endif