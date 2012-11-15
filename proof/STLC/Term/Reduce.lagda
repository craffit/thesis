%if False
\begin{code}
{-# OPTIONS --termination-depth=2 #-}
module STLC.Term.Reduce where

open import STLC.Term.Base
open import STLC.Term.Convertibility
open import STLC.Term.Operations.Simultaneous

open import Util.PropositionalEquality

import Relation.Binary.EqReasoning

_⟦·⟧_ : ∀ {Γ τ σ} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
_⟦·⟧_ (Λ f) a    = f / sub vz a
_⟦·⟧_ (var x) a  = var x · a
_⟦·⟧_ (f · x) a  = f · x · a

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
⟦ var y ⟧   = var y
⟦ Λ y ⟧     = Λ ⟦ y ⟧
⟦ y · y' ⟧  = ⟦ y ⟧ ⟦·⟧ ⟦ y' ⟧

⟦·⟧βη : ∀ {Γ τ τ'} → (t : Γ ⊢ τ ⇒ τ') → (t' : Γ ⊢ τ) → t · t' βη-≡ t ⟦·⟧ t'
⟦·⟧βη (Λ y) a     = beta
⟦·⟧βη (var y) a   = □
⟦·⟧βη (y · y') a  = □

evalβη : ∀ {Γ τ} → (t : Γ ⊢ τ) → t βη-≡ ⟦ t ⟧
evalβη (var y)   = □
evalβη (Λ y)     = %Λ (evalβη y)
evalβη (y · y')  =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ evalβη y %· evalβη y' ⟩
       _ ⟷⟨ ⟦·⟧βη ⟦ y ⟧ ⟦ y' ⟧ ⟩
       _ ∎
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