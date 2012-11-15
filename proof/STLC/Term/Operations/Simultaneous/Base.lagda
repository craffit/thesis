%if False

\begin{code}
module STLC.Term.Operations.Simultaneous.Base where

open import STLC.Variable
open import STLC.Term.Base
open import STLC.Term.Operations.Weaken

infix 3 _=>_

infixl 8 _/_
infixl 8 _≡/_
infixl 9 _/=>_

\end{code}
%endif

\subsection{Simultaneous substitution}
The STLC implementation of Keller and Altenkirch makes use of single substitution to implement evaluation and $\beta\eta$-equality. For our purpose we also require simultaneous substitution. Simultaneous substitution is a substitution technique in which all free variables in a term are replaced, at once, with terms belonging to an entirely new context. This is defined as follows:

\begin{code}

data _=>_ : Con → Con → Set where
  sz : ∀ {Δ}      → ε => Δ
  ss : ∀ {Γ Δ τ}  → Γ => Δ → Δ ⊢ τ → Γ , τ => Δ

\end{code}

The substitution type is indexed by two type contexts. The first type context represents the free variables that will be replaced and the second type context represents the new type context after substitution. This new type context is the type context for all substituted terms.


Before defining the function which will perform the actual substitution on terms, we need some auxiliary functions to manipulate simultaneous substitutions.

\begin{code}

wkS : ∀ {τ Γ Δ} → (x : Δ ∋ τ) → Γ => Δ - x → Γ => Δ
wkS v sz         = sz
wkS v (ss y y')  = ss (wkS v y) (wkTm v y')

extS : ∀ {τ Γ Δ} → (x : Γ ∋ τ) → (t : Δ ⊢ τ) → Γ - x => Δ → Γ => Δ
extS vz t s               = ss s t
extS (vs y) t (ss y' y0)  = ss (extS y t y') y0

wkExtS : {Γ Δ : Con} {τ : Ty} → (x : Γ ∋ τ) → (y : Δ ∋ τ) 
      → Γ - x => Δ - y → Γ => Δ
wkExtS x y v = extS x (var y) (wkS y v)
\end{code}

The |wkS| function weakens the result context of a substitution, the |extS| function extends a substitution such that it replaces an extra free variable with a term. |wkExtS| is defined for convenience to create a 'gap' in a substitution. This function adds a new free variable to a substitution which will be replaced by another newly created variable.



The substitution function |_/_| can now be defined in the following way, with use of helper function lookup. |lookup| retrieves the term at some variable index from a substitution.

\begin{code}
lookup : ∀ {Γ Δ τ} → (v : Γ ∋ τ) → Γ => Δ → Δ ⊢ τ
lookup vz (ss y y')       = y'
lookup (vs y) (ss y' y0)  = lookup y y'

_/_ : ∀ {Γ Δ τ} → Γ ⊢ τ → Γ => Δ → Δ ⊢ τ
_/_ (var y)   s = lookup y s
_/_ (Λ y)     s = Λ (y / wkExtS vz vz s)
_/_ (y · y')  s = (y / s) · (y' / s)

\end{code}

Using |lookup| the variable case becomes simple to implement. The interesting case is applying substitutions over lambda abstractions. Lambda abstraction binds a variable from the free variable context of its subterm. In order to be able to apply the given substitution to this subterm, we extend the given substitution with an identity substitution for the newly bound variable. The lambda bound variable will be replaced by itself. This is the desired working of capture-avoiding substitution: shadowed variables will not be changed.

Simultaneous substitutions can not only be applied to terms, but can be applied to other simultaneous substitutions as well. This is shown by the following function.

\begin{code}
_/=>_ : ∀ {Γ Δ Δ'} → Γ => Δ → Δ => Δ' → Γ => Δ'
sz       /=> s' = sz
ss y y'  /=> s' = ss (y /=> s') (y' / s')
\end{code}

      
\paragraph{Single substitution} Single substitution can be implemented using simultaneous substitution. Single substitution is needed in order to be able to implement $\beta$-reduction. A single substitution is created by extending the identity substitution with one free variable and a term.

\begin{code}

ι : ∀ {Γ} → Γ => Γ
ι {ε}       = sz
ι {y , y'}  = wkExtS vz vz (ι {y})

sub : ∀ {Γ τ} → (v : Γ ∋ τ) → (x : Γ - v ⊢ τ) → Γ => Γ - v
sub v x = extS v x ι

\end{code}

\begin{code}

open import Relation.Binary.PropositionalEquality

≡ss : ∀ {Γ Δ τ} {s s' : Γ => Δ} {t t' : Δ ⊢ τ} → s ≡ s' → t ≡ t' → ss s t ≡ ss s' t'
≡ss refl refl = refl

≡wkS : ∀ {Γ Δ τ} → (x : Δ ∋ τ) → {s s' : Γ => Δ - x} → s ≡ s' → wkS x s ≡ wkS x s'
≡wkS _ refl = refl

≡extS : ∀ {Γ Δ τ} →(x : Γ ∋ τ) → {t t' : Δ ⊢ τ} {s s' : Γ - x => Δ} → t ≡ t' → s ≡ s'
      → extS x t s ≡ extS x t' s'
≡extS _ refl refl = refl

≡lookup : ∀ {Γ Δ τ} {v v' : Γ ∋ τ} {s s' : Γ => Δ} → v ≡ v' → s ≡ s' 
        → lookup v s ≡ lookup v' s'
≡lookup refl refl = refl

_≡/_ : ∀ {Γ Δ τ} {t t' : Γ ⊢ τ} {s s' : Γ => Δ} → t ≡ t' → s ≡ s' → t / s ≡ t' / s'
refl ≡/ refl = refl
\end{code}
%endif
