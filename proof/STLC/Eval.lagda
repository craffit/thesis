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

-- Evaluation

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

Full normalization

\begin{code}
infixl 4 _↣_

data _↣_ : {Γ : Con} {τ : Ty} → Γ ⊢ τ → Γ ⊢ τ → Set where
  lamc  : ∀ {Γ σ τ} {t1 t2 : Γ , σ ⊢ τ} → t1 ↣ t2 → Λ t1 ↣ Λ t2
  left  : ∀ {Γ σ τ} {t : Γ ⊢ σ} {t1 t2 : Γ ⊢ σ ⇒ τ} {t3 : Γ ⊢ τ} 
            → t1 ↣ t2 → t2 · t ↣ t3 → t1 · t ↣ t3
  right : ∀ {Γ σ τ} {t1 t2 : Γ ⊢ σ} {t : Γ ⊢ σ ⇒ τ} {t3 : Γ ⊢ τ} 
            → t1 ↣ t2 → t · t2 ↣ t3 → t · t1 ↣ t3
  beta  : ∀ {Γ σ τ} {t1 : Γ , σ ⊢ τ} {t2 : Γ ⊢ σ} {t3 : Γ ⊢ τ} → t1 / sub vz t2 ↣ t3 → Λ t1 · t2 ↣ t3

↣-βη : ∀ {Γ τ} {t1 t2 : Γ ⊢ τ} → t1 ↣ t2 → t1 βη-≡ t2
↣-βη (lamc y)     = congΛ (↣-βη y)
↣-βη (left y y')  = btrans (congApp (↣-βη y) brefl) (↣-βη y')
↣-βη (right y y') = btrans (congApp brefl (↣-βη y)) (↣-βη y')
↣-βη (beta y)     = btrans beta (↣-βη y)
\end{code}