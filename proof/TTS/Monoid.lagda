%if False
\begin{code}
open import STLC

open import TTS.Functor.Base
open import TTS.Context.Base
open import TTS.Rules.Base
import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

\end{code}
%endif

The monoid transformation is parametrized is parametrized by a monoidal structure: A type, the two operations and the accompanying laws. For this transformation we actually only need the right-identity of the mplus operation, so it is a bit more liberal than a normal monoid.

\begin{code}
module TTS.Monoid  (A : ℕ) (mzero : ε ⊢ C A)
                   (mplus : ε ⊢ C A ⇒ C A ⇒ C A)
                   (assoc  :     ∀ {Γ} (a₁ a₂ a₃ : Γ ⊢ C A)
                           →     up mplus · (up mplus · a₁ · a₂) · a₃
                           βη-≡  up mplus · a₁ · (up mplus · a₂ · a₃))
                   (right-identity  :  ∀ {Γ} (e : Γ ⊢ C A)
                                    →  up mplus · e · up mzero βη-≡ e) where
\end{code}

Based on this monoid the ingredients for the transformation can be defined. The representation type |R| is constructed as a function over the monoidal type, analogous to Hughes' strings, the |abs| and |rep| function ae constructed accordingly. The transformation has just one rule which converts the binary operator into function composition.

\begin{code}
R : Ty
R = C A ⇒ C A

abs : ε ⊢ R ⇒ C A
abs = Λ (v 0 · up mzero)

rep : ε ⊢ C A ⇒ R
rep = Λ (up mplus · v 0)

rules : Rules A R
rules = replace {A} {R} {Id ⟶ Id ⟶ Id} ε mplus comp

import TTS.Judgement.Base
open TTS.Judgement.Base A R rep abs rules

\end{code}

This gives rise to a basic type and transform system for monoids. To show that this transformation actually preserves the  semantics, we have to show that the |abs| and |rep| function form a retraction, and that the |mplus| to |`comp`| transformation preserves the logical relation.

\begin{code}
abs-rep : abs ∘ rep βη-≡ id
abs-rep =
  let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ eval-comp _ _ ⟩
     _ ⟷⟨  %Λ (%Λ (□ %· %≡ wk-up (vs vz) mzero)
            %· (%Λ (%≡ wk-up (vs vz) mplus %· □) %· □)) ⟩
     _ ⟷⟨ %Λ (□ %· beta ⟷ (%≡ up-id mplus _ %· □)) ⟩
     _ ⟷⟨ %Λ beta ⟩
     _ ⟷⟨ %Λ (□ %· %≡ up-id mzero _) ⟩
     _ ⟷⟨ %Λ right-identity (var vz) ⟩
     _ ∎
\end{code}

%if False
\begin{code}
import TTS.Relation
open TTS.Relation A R rep

import TTS.Rules.Proof
open TTS.Rules.Proof A R rep
\end{code}
%endif

The logical relation contains only base types. Proving can thus be done using equational reasoning.

\begin{code}
m-rel : rel {ε} {Id ⟶ Id ⟶ Id} mplus comp ε ε
m-rel a a' r a0 a1 r1 =
  let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %Λ (%≡ merge-/ mplus _ _ %· □) %· □ ⟩
     _ ⟷⟨ beta ⟩
     _ ⟷⟨ %≡ merge-/ mplus _ _ %· □ ⟩
     _ ⟷⟨ bsym eta ⟷ %Λ (%≡ wk-up vz (mplus · (mplus · a · a0)) %· □) ⟩
     _ ⟷⟨ %Λ assoc (up a) (up a0) (v 0) ⟩
     _ ⟷⟨ %Λ (%≡ split-/ mplus _ _ %· □ %· (%≡ split-/ mplus _ _ %· □ %· □)) ⟩
     _ ⟷⟨ %Λ (bsym beta %· (bsym beta %· □)) ⟩
     _ ⟷⟨  %Λ (%Λ (bsym (%≡ wk-up _ mplus) %· □) %· bsym (%≡ wk-up _ a)
           %· (%Λ (bsym (%≡ wk-up _ mplus) %· □) %· bsym (%≡ wk-up _ a0) %· □))
           ⟩
     _ ⟷⟨ bsym (eval-comp _ _) ⟩
     _ ⟷⟨  %Λ (%≡ split-/ mplus _ _ %· □)
            %· □ %∘ %Λ (%≡ split-/ mplus _ _ %· □) %· □ ⟩
     _ ⟷⟨ r %∘ r1 ⟩
     _ ∎

proofs : RuleProofs rules
proofs = proof ε mplus comp m-rel

\end{code}

%if False
\begin{code}
import TTS.Judgement.Properties
open TTS.Judgement.Properties A R rep abs rules

import TTS.Properties
open TTS.Properties A R rep abs rules
\end{code}
%endif

\begin{code}
open TransformationProof abs-rep proofs
\end{code}

We can use this to show the equivalence of transformed terms.

\begin{code}
trans₁ : (ε , C A) ∶ C A  ⊨ up mplus · v 0 · v 0
                          ↝ (up abs · (up rep · v 0 ∘ up rep · v 0))
trans₁ = i-abs (app (app (rule (rule ε)) (i-rep (var vz))) (i-rep (var vz)))

proof₁ : (s : (ε , C A) ↓)  →     close (up mplus · v 0 · v 0) s
                            βη-≡  close (up abs · (up rep · v 0 ∘ up rep · v 0)) s
proof₁ =  extract {ε , C A} {A}
    (up mplus · v 0 · v 0)
    (up abs · (up rep · v 0 ∘ up rep · v 0))
    (≡! sym (!,⊢-id (ε , C A) (C A) _) , sym (!,⊢-id (ε , C A) (C A) _) >↝ trans₁)
\end{code}

%if False
\begin{code}
trans₂ : (ε , C A) ∶ C A  ⊨ (Λ (up mplus · v 1 · v 0)) · v 0
                          ↝ (up abs · (Λ (up rep · v 1 ∘ v 0) · (up rep · v 0)))
trans₂ = i-abs (app (lam (app (app (rule (rule ε)) (i-rep (var (vs vz)))) (var vz))) (i-rep (var vz)))

proof₂ : (s : (ε , C A) ↓)  →     close ((Λ (up mplus · v 1 · v 0)) · v 0) s
                            βη-≡  close (up abs · (Λ (up rep · v 1 ∘ v 0) · (up rep · v 0))) s
proof₂ = extract {ε , C A} {A} ((Λ (up mplus · v 1 · v 0)) · v 0) (up abs · (Λ (up rep · v 1 ∘ v 0) · (up rep · v 0))) (≡! sym (!,⊢-id (ε , C A) (C A) _) , sym (!,⊢-id (ε , C A) (C A) _) >↝ trans₂)

\end{code}
%endif
