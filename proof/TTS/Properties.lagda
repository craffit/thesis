%if False
\begin{code}

open import STLC
open import TTS.Rules.Base

module TTS.Properties  
  (A : ℕ) (R : Ty) 
  (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A)
  (rules : Rules A R)
   where

open import TTS.Functor.Base
open import TTS.Context.Base
import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

import TTS.Judgement
open TTS.Judgement A R rep abs rules
import TTS.Relation
open TTS.Relation A R rep
import TTS.Rules.Proof
open TTS.Rules.Proof A R rep
\end{code}
%endif

As said, a program transformation is only semantics preserving for types which form a retraction and when the transformation rules are related. This is expressed by proving within a parametrized module:

\begin{code}
module  TransformationProof  (abs-rep : abs ∘ rep βη-≡ id) 
                             (proofs : RuleProofs rules) where
\end{code}

Within this parametrized module we can now show the fundamental theorem and extraction theorem. The fundamental theorem shows that a type and transform system transformation is logically related under related environments.

\begin{code}  
  fundament  : ∀ {φ Φ e e'} → (v : φ ∶ Φ ⊨ e ↝ e') → (s : ⟦ φ ⟧φ C A ↓) 
             → (s' : ⟦ φ ⟧φ R ↓) → Rel↓ φ s s' → rel {φ} {Φ} e e' s s'
\end{code}

%if False
\begin{code}
  fundament {ε} (var ()) s s' r
  fundament {φ , Φ} (var vz) (cls s e) (cls s' e') (cls y y') = 
        cross-left {φ} {Φ} (var vz) (var vz) s s' e e' y'
  fundament {φ , Φ'} {Φ} (var (vs y)) (cls s e) (cls s' e') (cls y' y0) = 
          cross-left {φ} {Φ} _ _ s s' e e' 
       (  ≡rel {φ} {Φ} (sym (I-lookup _)) (sym (I-lookup _)) refl refl 
       (  fundament (var y) s s' y'))
  fundament (app y y') s s' r = fundament y s s' r _ _ (fundament y' s s' r)
  fundament (lam {φ} {Φ'} {Φ} {e} {e'} y) s s' r = 
       λ a a' ra  →  rel-βη {φ} {Φ} s s' (bsym beta) (bsym beta) 
                  (  cross-right {φ} {Φ} e e' s s' a a' 
                  (  fundament y _ _ (cls r ra)))
  fundament (i-rep y) s s' r = %≡ split-/ rep sz (↓-=> s') %· fundament y s s' r
  fundament (i-abs y) s s' r =
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
      _ ⟷⟨ bsym beta ⟩
      _ ⟷⟨ %up (bsym abs-rep) %· □ ⟩
      _ ⟷⟨ do-comp _ _ _ ⟩
      _ ⟷⟨ %≡ split-/ abs sz (↓-=> s') %· fundament y s s' r ⟩
      _ ∎
  fundament {φ} {Φ} (rule ru) s s' r' = rel-up {φ} {Φ} _ _ s s' (getProof ru proofs)
\end{code}
%endif

To show the extraction theorem, we first need to show that a closing environment is related to itself. This follows from the fact that we can construct an identity transformation for each term. The fundamental theorem then shows that the transformation is related.

\begin{code}  
  relΓ : ∀ {Γ} → (s : Γ ↓) → Rel↓ (Γ ↑φ) (! ↑φ-≡Γ >↓ s) (! ↑φ-≡Γ >↓ s)
  relΓ ε           = ε
  relΓ (cls y y')  = cls (relΓ y) (fundament (id↝ y') _ _ (relΓ y))
\end{code}

Using these two lemmas we can show the final extraction Lemma, showing that a complete transformation yields equivalent terms under any closing environment. 
  
\begin{code}
  extract  : ∀ {Γ n} → (e e' : Γ ⊢ C n)
           → Γ ↑φ ∶ C n ⊨ ! ↑φ-≡Γ , ≡τrefl >⊢ e ↝ ! ↑φ-≡Γ , ≡τrefl >⊢ e'
           → (s : Γ ↓) → close e s βη-≡ close e' s
\end{code}

The fact that the transformation is complete is enforce by the constant Functor |C n| and the fact that the functor context should be lifted from some normal context |Γ|. The |! ↑φ-≡Γ , ≡τrefl >⊢| term proves that the interpretation of a lifted term context is equal to the base context.

This mechanically proves that the type and transform system is semantics preserving.

%if False
\begin{code}
  extract {Γ} {n} e e' v s =
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
      _ ⟷⟨ %≡ sym (!,⊢-id ε (C n) _) ⟩
      _ ⟷⟨ %≡ !,⊢-close ↑φ-≡Γ (C n) e s ⟩
      _ ⟷⟨ fundament v _ _ (relΓ s) ⟩
      _ ⟷⟨ %≡ sym (!,⊢-close ↑φ-≡Γ (C n) e' s) ⟩
      _ ⟷⟨ %≡ !,⊢-id ε (C n) _ ⟩
      _ ∎
\end{code}
%endif