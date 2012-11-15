\begin{code}
open import STLC

module TTS.Monoid (A : ℕ) (mplus : ε ⊢ C A ⇒ C A ⇒ C A) (mzero : ε ⊢ C A)
  (assoc : ∀ {Γ} (a₁ a₂ a₃ : Γ ⊢ C A) 
   → up mplus · (up mplus · a₁ · a₂) · a₃ βη-≡ up mplus · a₁ · (up mplus · a₂ · a₃))
  (right-identity : ∀ {Γ} (e : Γ ⊢ C A) → up mplus · e · up mzero βη-≡ e) where

open import TTS.Functor.Base
open import TTS.Context.Base

R : Ty
R = C A ⇒ C A

abs : ε ⊢ R ⇒ C A 
abs = Λ (v 0 · up mzero)

rep : ε ⊢ C A ⇒ R
rep = Λ (up mplus · v 0)

import TTS.Rules
open TTS.Rules A R rep

import TTS.Relation
open TTS.Relation A R rep

import Relation.Binary.EqReasoning

abs-rep : abs ∘ rep βη-≡ id
abs-rep =
  let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ eval-comp _ _ ⟩
     _ ⟷⟨ %Λ (%Λ (□ %· %≡ wk-up (vs vz) mzero) %· (%Λ (%≡ wk-up (vs vz) mplus %· □) %· □)) ⟩
     _ ⟷⟨ %Λ (□ %· beta ⟷ (%≡ up-id mplus _ %· □)) ⟩
     _ ⟷⟨ %Λ beta ⟩
     _ ⟷⟨ %Λ (□ %· %≡ up-id mzero _) ⟩
     _ ⟷⟨ %Λ right-identity (var vz) ⟩
     _ ∎

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
     _ ⟷⟨ %Λ (%Λ (bsym (%≡ wk-up _ mplus) %· □) %· bsym (%≡ wk-up _ a) %· (%Λ (bsym (%≡ wk-up _ mplus) %· □) %· bsym (%≡ wk-up _ a0) %· □)) ⟩
     _ ⟷⟨ bsym (eval-comp _ _) ⟩
     _ ⟷⟨ %Λ (%≡ split-/ mplus _ _ %· □) %· □ %∘ %Λ (%≡ split-/ mplus _ _ %· □) %· □ ⟩
     _ ⟷⟨ r %∘ r1 ⟩
     _ ∎

rules : Rules
rules = replace {Id ⟶ Id ⟶ Id} ε mplus comp m-rel

import TTS.Properties
open TTS.Properties A R rep abs abs-rep
open RuleProof rules

\end{code}
