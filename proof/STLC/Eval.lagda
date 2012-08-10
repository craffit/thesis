%if False
\begin{code}
{-# OPTIONS --termination-depth=2 #-}
module STLC.Eval where

open import STLC.Base public
open import STLC.SSubst public
open import STLC.Equality

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

import Relation.Binary.EqReasoning
\end{code}
%endif

\begin{code}

_⟦·⟧_ : ∀ {Γ τ σ} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
_⟦·⟧_ (Λ f) a    = f / sub vz a
_⟦·⟧_ (var x) a  = var x · a
_⟦·⟧_ (f · x) a  = f · x · a

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
⟦ var y ⟧   = var y
⟦ Λ y ⟧     = Λ ⟦ y ⟧
⟦ y · y' ⟧  = ⟦ y ⟧ ⟦·⟧ ⟦ y' ⟧

\end{code}

%if False
\begin{code}
⟦·⟧βη : ∀ {Γ τ τ'} → (t : Γ ⊢ τ ⇒ τ') → (t' : Γ ⊢ τ) → t · t' βη-≡ t ⟦·⟧ t'
⟦·⟧βη (Λ y) a     = beta
⟦·⟧βη (var y) a   = brefl
⟦·⟧βη (y · y') a  = brefl

evalβη : ∀ {Γ τ} → (t : Γ ⊢ τ) → t βη-≡ ⟦ t ⟧
evalβη (var y)   = brefl
evalβη (Λ y)     = congΛ (evalβη y)
evalβη (y · y')  =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
         y · y'
       ⟷⟨ congApp (evalβη y) (evalβη y') ⟩
         ⟦ y ⟧ · ⟦ y' ⟧
       ⟷⟨ ⟦·⟧βη ⟦ y ⟧ ⟦ y' ⟧ ⟩
         ⟦ y · y' ⟧
       ∎
\end{code}
%endif

\begin{code}
β≡ : ∀ {Γ τ} → {t t' : Γ ⊢ τ} → ⟦ t ⟧ βη-≡ ⟦ t' ⟧ → t βη-≡ t'
β≡ {_} {_} {t} {t'} eqp =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
         t
       ⟷⟨ evalβη t ⟩
         ⟦ t ⟧
       ⟷⟨ eqp ⟩
         ⟦ t' ⟧
       ⟷⟨ bsym (evalβη t') ⟩
         t'
       ∎

\end{code}