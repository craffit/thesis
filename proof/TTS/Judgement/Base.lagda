%if False
\begin{code}

open import STLC public
open import TTS.Rules.Base

open import Util.PropositionalEquality

open import TTS.Functor.Base
open import TTS.Context.Base

\end{code}
%endif
\noindent \paragraph{|(TTS(stlc))|} is intended to be a base system for type-changing transformations, independent of which types and terms are changed. In other words, |(TTS(stlc))| should be parametrizable with different types and rewriting rules. In Agda this can be expressed using parametrized modules. The base system is parametrized by the source and result type |A| and |R|, together with the |abs| and |rep| functions to convert between them. Additionally a set of rules is expected which perform the actual transformations.

\begin{code}
module TTS.Judgement.Base 
       (A : ℕ) (R : Ty) 
       (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A) 
       (rules : Rules A R)
         where

\end{code}

The inductive family representing |(TTS(stlc))| now looks as follows:

\begin{code}

infix 1 _∶_⊨_↝_
  
data _∶_⊨_↝_  : (φ : Ftx) → (Φ : Functor) → (e : ⟦ φ ⟧φ C A ⊢ ⟦ Φ ⟧Φ C A)
              → (e' : ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R) → Set where
     var     : ∀ {φ Φ} (v : φ ∋φ Φ)
             → φ ∶ Φ ⊨ var (⟦ v ⟧∋ C A) ↝ var (⟦ v ⟧∋ R)
     app     : ∀ {φ Φ₁ Φ₂ e₁ e₁' e₂ e₂'} 
             → φ ∶ Φ₁ ⟶ Φ₂ ⊨ e₁ ↝ e₁' → φ ∶ Φ₁ ⊨ e₂ ↝ e₂' 
             → φ ∶ Φ₂ ⊨ e₁ · e₂ ↝ e₁' · e₂'
     lam     : ∀ {φ Φ₁ Φ₂ e e'} → φ , Φ₁ ∶ Φ₂ ⊨ e ↝ e' → φ ∶ Φ₁ ⟶ Φ₂ ⊨ Λ e ↝ Λ e'
     i-rep   : ∀ {φ e e'} → φ ∶ C A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ up rep · e'
     i-abs   : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ C A ⊨ e ↝ up abs · e' 
     rule    : ∀ {φ Φ e e'} → Rule {Φ} e e' rules → φ ∶ Φ ⊨ up e ↝ up e'

\end{code}

The inductive family closely follows the specification from chapter~\ref{chap:tts}. In the judgement the functor is moved in front of the converted terms, because scoping in Agda is from left to right.

This definition shows clearly how two terms are typed by one typing functor and functor context. The |var|, |app| and |lam| rules just propagate these type changes using the rules of the simply typed lambda calculus. The |i-rep|, |i-abs| and |rule| construction actually have the power to change the types and terms.

