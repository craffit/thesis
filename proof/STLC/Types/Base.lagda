\begin{code}

module STLC.Types.Base where

open import Data.Nat public
open import Relation.Binary.PropositionalEquality

infixr 6 _⇒_ 
infixr 6 _≡⇒_ 

data Ty : Set where
  C    : ℕ → Ty
  _⇒_  : Ty → Ty → Ty

≡C : ∀ {a b} → a ≡ b → C a ≡ C b
≡C = cong C

_≡⇒_ : ∀ {a b c d} → a ≡ b → c ≡ d → a ⇒ c ≡ b ⇒ d
_≡⇒_ = cong₂ _⇒_
 
inj-C : ∀ {a b} → C a ≡ C b → a ≡ b
inj-C refl = refl

⇒-inj-left : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → a ≡ b
⇒-inj-left refl = refl 

⇒-inj-right : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → c ≡ d
⇒-inj-right refl = refl 

\end{code}