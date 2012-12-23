{-# OPTIONS --termination-depth=20 #-}
\begin{code}

open import STLC

module TTS.Properties2  (A : ℕ) (R : Ty) 
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
  open RuleJudgement rules public
  
  data Re : (φ : Ftx) → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) → Set where

  prop : ∀ {φ Φ e e'} → (v : φ ∶ Φ ⊨ e ↝ e') → (s : ⟦ φ ⟧Γ (C A) ↓) 
     → (s' : ⟦ φ ⟧Γ R ↓) 
     → Re φ s s' → dimap Φ · abs · rep · close e s βη-≡ close e' s'
  prop (TTS.Judgement.RuleJudgement.var v) s s' r = {!!}
  prop (TTS.Judgement.RuleJudgement.app y y') s s' r = {!!}
  prop (TTS.Judgement.RuleJudgement.lam y) s s' r =
    let open Relation.Binary.EqReasoning βηsetoid
             renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
      _ ⟷⟨ bsym eta ⟩
      _ ⟷⟨ {!!} ⟩
      _ ∎
  prop (TTS.Judgement.RuleJudgement.i-rep y) s s' r = {!!}
  prop (TTS.Judgement.RuleJudgement.i-abs y) s s' r = {!!}
  prop (TTS.Judgement.RuleJudgement.rule y) s s' r = {!!}
\end{code}