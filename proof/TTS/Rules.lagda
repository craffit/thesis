\begin{code}

open import STLC
open import STLC.Pattern.Base

module TTS.Rules  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

import TTS.Relation.Base
open TTS.Relation.Base A R rep

open import TTS.Functor.Base
open import TTS.Context.Base
open import Util.PropositionalEquality

data Rules : Set where
  ε        : Rules
  replace  : ∀ {Φ} → (r : Rules) → (e : ε ⊢ ⟦ Φ ⟧Φ (C A)) 
           → (e' : ε ⊢ ⟦ Φ ⟧Φ R) → Rules

data Rule {Φ} (e : ε ⊢ ⟦ Φ ⟧Φ (C A)) (e' : ε ⊢ ⟦ Φ ⟧Φ R) : Rules → Set where
  rule : ∀ rs → (r : rel {ε} {Φ} e e' ε ε) → Rule e e' (replace {Φ} rs e e' r)
  skip : ∀ {rs Φ' f f'} {r : rel {ε} {Φ'} f f' ε ε} 
       → (ru : Rule {Φ} e e' rs ) → Rule e e' (replace {Φ'} rs f f' r)

ruleRel : ∀ {rs Φ e e'} → Rule {Φ} e e' rs → rel {ε} {Φ} e e' ε ε
ruleRel (rule rs r) = r
ruleRel (skip rs) = ruleRel rs

{-
data Patφ (φ φ' : Ftx) : (Φ : Functor) → Set where
  var   : ∀ {Φ}  → (v : φ ∋↝ Φ) → Patφ φ φ' Φ
  pvar  : ∀ {Φ}   → (v : φ' ∋↝ Φ) → Patφ φ φ' Φ
  _·_   : ∀ {Φ Φ'} → Patφ φ φ' (Φ ⟶ Φ') → Patφ φ φ' Φ → Patφ φ φ' Φ'

⟦_⟧P : ∀ {φ φ' Φ} → Patφ φ φ' Φ → (a : Ty) → Pat (⟦ φ ⟧Γ a) (⟦ φ' ⟧Γ a) (⟦ Φ ⟧Φ a)
⟦_⟧P (var v) a = var (⟦ v ⟧∋ a)
⟦_⟧P (pvar v) a = pvar (⟦ v ⟧∋ a)
⟦_⟧P (y · y') a = ⟦ y ⟧P a · ⟦ y' ⟧P a

wkPatφ : ∀ {Φ' φ φ' Φ} → Patφ φ φ' Φ → Patφ (φ , Φ') φ' Φ
wkPatφ (var v)  = var (wkv∋↝ vz v)
wkPatφ (pvar v) = pvar v
wkPatφ (y · y') = wkPatφ y · wkPatφ y'
{-
patAppφ : ∀ {Γ Γ' τ} → Pat Γ Γ' τ → Γ' => Γ → Γ ⊢ τ
patAppφ (var v) s  = var v
patAppφ (pvar v) s = lookup v s
patAppφ (y · y') s = patAppφ y s · patAppφ y' s
-}

data Rewrites (φ : Ftx) : Set where
  ε    : Rewrites φ
  rewr : ∀ {φ' Φ Φ'} → Rewrites φ → (p : Patφ φ φ' Φ) → (p' : Patφ φ φ' Φ')
       → Rewrites φ

wkRewrites : ∀ {Φ φ} → Rewrites φ → Rewrites (φ , Φ)
wkRewrites ε = ε
wkRewrites (rewr y p p') = rewr (wkRewrites y) (wkPatφ p) (wkPatφ p')

data Rewrite {φ} {φ'} {Φ} {Φ'} (p : Patφ φ φ' Φ) (p' : Patφ φ φ' Φ') 
     : Rewrites φ → Set where
  rewr : ∀ {ps} → Rewrite p p' (rewr ps p p')
  skip :  ∀ {ps φ₁ Φ₁ Φ₂} {p₁ : Patφ φ φ₁ Φ₁} {p₂ : Patφ φ φ₁ Φ₂} 
       → Rewrite p p'  ps
       → Rewrite p p' (rewr ps p₁ p₂)
-}
\end{code}