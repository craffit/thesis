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

A program transformation is only semantics preserving for types which form a retraction and for transformation rules which are related. This is expressed by proving within a parametrized module:

\begin{code}
module  TransformationProof  (abs-rep : abs ∘ rep βη-≡ id) 
                             (proofs : RuleProofs rules) where
\end{code}

In the context of the Curry-Howard correspondence a module parameter can be seen as an assumption in logic. In this case we assume |abs| and |rep| to form a retraction and all the rules to adhere to the logical relation.

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

From this follows the corollary that a closing environment is related to itself. This follows from the fact that we can construct an identity transformation for each term in the closing environment. The fundamental theorem then shows that the transformation is related.

%if False
\begin{code}  
{-
\end{code}
%endif

\begin{code}  
  relΓ : ∀ {Γ} → (s : Γ ↓) → Rel↓ (Γ ↑φ) s s
  relΓ ε           = ε
  relΓ (cls y y')  = cls (relΓ y) (fundament (id↝ y') _ _ (relΓ y))
\end{code}

%if False
\begin{code}  
-}
\end{code}
%endif

%if False
\begin{code}  
  relΓ : ∀ {Γ} → (s : Γ ↓) → Rel↓ (Γ ↑φ) (! ↑φ-≡Γ >↓ s) (! ↑φ-≡Γ >↓ s)
  relΓ ε           = ε
  relΓ (cls y y')  = cls (relΓ y) (fundament (id↝ y') _ _ (relΓ y))
  \end{code}
%endif

 The extraction lemma establishes that for base types the logical relation implies that the two related terms are $\beta\eta$-equivalent. This follows immediately form the definition of the logical relation. For base types the logical relation defines the $\beta\eta$-equivalence we are trying to prove.

%if False
\begin{code}  
{-
\end{code}
%endif

\begin{code}  
  extract  : ∀ {Γ n} → (e e' : Γ ⊢ C n) → (s s' : Γ ↓) 
           → rel {Γ ↑φ} {C n} e e' s s' → close e s βη-≡ close e' s'
  extract {Γ} {n} e e' s s' r = r
\end{code}

%if False
\begin{code}  
-}
\end{code}
%endif


%if False
\begin{code}    
  extract  : ∀ {Γ n} → (e e' : Γ ⊢ C n) → (s s' : Γ ↓) 
        → rel {Γ ↑φ} {C n} (! ↑φ-≡Γ , ≡τrefl >⊢ e) (! ↑φ-≡Γ , ≡τrefl >⊢ e') 
                           (! ↑φ-≡Γ >↓ s) (! ↑φ-≡Γ >↓ s') 
        → close e s βη-≡ close e' s'
  extract {Γ} {n} e e' s s' r = 
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ %≡ sym (!,⊢-id ε (C n) (close e s)) ⟩
       _ ⟷⟨ %≡ !,⊢-close ↑φ-≡Γ (C n) e s ⟩
       _ ⟷⟨ r ⟩
       _ ⟷⟨ %≡ sym (!,⊢-close ↑φ-≡Γ (C n) e' s') ⟩
       _ ⟷⟨ %≡ !,⊢-id ε (C n) (close e' s') ⟩
       _ ∎
\end{code}
%endif

Using these three lemmas we can prove the final equivalence Theorem: proving that a complete transformation yields equivalent terms under any closing environment. 

%if False
\begin{code}  
{-
\end{code}
%endif

\begin{code}
  equivalence  : ∀ {Γ n} → (e e' : Γ ⊢ C n) → (s : Γ ↓) 
               → Γ ↑φ ∶ C n ⊨ e ↝ e' → close e s βη-≡ close e' s
  equivalence e e' v s = extract e e' s s (fundament v _ _ (relΓ s)) 
\end{code}

%if False
\begin{code}  
-}
\end{code}
%endif

The fact that the transformation is complete is enforced by the base type functor |(C n)| and the fact that the functor context should be lifted from some normal context |Γ|. This mechanically proves that the type and transform system is semantics preserving.

%if False
\begin{code}
  equivalence  : ∀ {Γ n} → (e e' : Γ ⊢ C n)
           → Γ ↑φ ∶ C n ⊨ ! ↑φ-≡Γ , ≡τrefl >⊢ e ↝ ! ↑φ-≡Γ , ≡τrefl >⊢ e'
           → (s : Γ ↓) → close e s βη-≡ close e' s
  equivalence e e' v s = extract e e' s s (fundament v _ _ (relΓ s)) 
\end{code}
%endif