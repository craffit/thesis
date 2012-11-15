{-# OPTIONS --termination-depth=20 #-}
\begin{code}

open import STLC

module TTS.Properties  (A : ℕ) (R : Ty) 
  (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A)
  (abs-rep : abs ∘ rep βη-≡ id) where

open import TTS.Functor.Base
open import TTS.Context.Base
import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

import TTS.Judgement
open TTS.Judgement A R rep abs
import TTS.Relation
open TTS.Relation A R rep

module RuleProof (rules : Rules) where
  open RuleJudgement rules

  inrel : ∀ {φ Φ e e'} → (v : φ ∶ Φ ⊨ e ↝ e') → (s : ⟦ φ ⟧Γ (C A) ↓) 
        → (s' : ⟦ φ ⟧Γ R ↓) → Rel↓ φ s s' → rel {φ} {Φ} e e' s s'
  inrel {ε} (var ()) s s' r
  inrel {φ , Φ} (var vz) (cls s e) (cls s' e') (cls y y') = rel-sub-cls {φ} {Φ} (var vz) (var vz) s s' e e' y'
  inrel {φ , Φ'} {Φ} (var (vs y)) (cls s e) (cls s' e') (cls y' y0) = rel-sub-cls {φ} {Φ} _ _ s s' e e' (≡rel {φ} {Φ} (sym (ι-lookup _)) (sym (ι-lookup _)) refl refl (inrel (var y) s s' y'))
  inrel (app y y') s s' r = inrel y s s' r _ _ (inrel y' s s' r)
  inrel (lam {φ} {Φ'} {Φ} {e} {e'} y) s s' r = λ a a' ra → rel-βη {φ} {Φ} s s' (bsym beta) (bsym beta) (rel-cls-sub {φ} {Φ} e e' s s' a a' (inrel y _ _ (cls r ra)))
  inrel (i-rep y) s s' r = %≡ split-/ rep sz (↓-=> s') %· inrel y s s' r
  inrel (i-abs y) s s' r =
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
      _ ⟷⟨ bsym beta ⟩
      _ ⟷⟨ %up (bsym abs-rep) %· □ ⟩
      _ ⟷⟨ do-comp _ _ _ ⟩
      _ ⟷⟨ %≡ split-/ abs sz (↓-=> s') %· inrel y s s' r ⟩
      _ ∎
  inrel {φ} {Φ} (rule ru) s s' r' = rel-up {φ} {Φ} _ _ s s' (ruleRel ru)
  
  relΓ : ∀ {Γ} → (s : Γ ↓) → Rel↓ (Γ ↑φ) (! ↑φ-≡Γ >↓ s) (! ↑φ-≡Γ >↓ s)
  relΓ ε = ε
  relΓ (cls y y') = cls (relΓ y) (inrel (id↝ y') _ _ (relΓ y))

  trans-eq : ∀ {Γ n} → (e e' : Γ ⊢ C n) → (s : Γ ↓) 
           → Γ ↑φ ∶ K n ⊨ (! ↑φ-≡Γ , ≡τrefl >⊢ e) ↝ (! ↑φ-≡Γ , ≡τrefl >⊢ e')
           → close e s βη-≡ close e' s
  trans-eq {Γ} {n} e e' s v =
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
      _ ⟷⟨ %≡ sym (!,⊢-id ε (C n) _) ⟩
      _ ⟷⟨ %≡ !,⊢-close ↑φ-≡Γ (C n) e s ⟩
      _ ⟷⟨ inrel v _ _ (relΓ s) ⟩
      _ ⟷⟨ %≡ sym (!,⊢-close ↑φ-≡Γ (C n) e' s) ⟩
      _ ⟷⟨ %≡ !,⊢-id ε (C n) _ ⟩
      _ ∎

\end{code}