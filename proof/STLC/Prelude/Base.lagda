%if False
\begin{code}
module STLC.Prelude.Base where

open import STLC.Term

idε : ∀ {a} → ε ⊢ a ⇒ a
idε = Λ (var vz)

const' : ∀ {a b Γ} → Γ ⊢ b ⇒ a ⇒ a
const' = up (Λ (Λ (v 0)))

flip : ∀ {a b c Γ} → Γ ⊢ (a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c
flip = up (Λ (Λ (Λ (v 2 · v 0 · v 1))))

\end{code}
%endif

\begin{code}

id : ∀ {a Γ} → Γ ⊢ a ⇒ a
id = Λ (v 0)

const : ∀ {a b Γ} → Γ ⊢ a ⇒ b ⇒ a
const = Λ (Λ (v 1))

comp : ∀ {Γ a b c} → Γ ⊢ (b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
comp = Λ (Λ (Λ (v 2 · (v 1 · v 0))))

infixl 2 _∘_
_∘_ : ∀ {a b c Γ} → Γ ⊢ b ⇒ c → Γ ⊢ a ⇒ b → Γ ⊢ a ⇒ c
t1 ∘ t2 = comp · t1 · t2

\end{code}
