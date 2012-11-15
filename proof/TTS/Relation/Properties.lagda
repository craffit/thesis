{-# OPTIONS --termination-depth=20 #-}
\begin{code}

open import STLC

module TTS.Relation.Properties  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

import TTS.Relation.Base
open TTS.Relation.Base A R rep

open import TTS.Functor.Base
open import TTS.Context.Base
import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

mutual
  rel-sub-cls : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧Γ (C A) , ⟦ Φ' ⟧Φ (C A) ⊢ ⟦ Φ ⟧Φ (C A)) 
            → (e' :  ⟦ φ ⟧Γ R , ⟦ Φ' ⟧Φ R ⊢ ⟦ Φ ⟧Φ R) 
            → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) 
            → (a : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ' ⟧Φ (C A)) → (a' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ' ⟧Φ R)
            → rel {φ} {Φ} (e / sub vz a) (e' / sub vz a') s s'
            → rel {φ , Φ'} {Φ} e e' (cls s a) (cls s' a') 
  rel-sub-cls {φ} {Id} e e' s s' a a' r =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ □ %· e -%/ ss (=>≡ (sym (ι/=> (↓-=> s)))) □ ⟩
     _ ⟷⟨ □ %· %≡ split-/ e (ss ι a) (↓-=> s) ⟩
     _ ⟷⟨ r ⟩
     _ ⟷⟨ %≡ merge-/ e' (ss ι a') (↓-=> s') ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (ι/=> (↓-=> s'))) □ ⟩
     _ ∎
  rel-sub-cls {φ} {K τ} e e' s s' a a' r =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ e -%/ ss (=>≡ (sym (ι/=> (↓-=> s)))) □ ⟩
     _ ⟷⟨ %≡ split-/ e (ss ι a) (↓-=> s) ⟩
     _ ⟷⟨ r ⟩
     _ ⟷⟨ %≡ merge-/ e' (ss ι a') (↓-=> s') ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (ι/=> (↓-=> s'))) □ ⟩
     _ ∎
  rel-sub-cls {φ} {Φ₁ ⟶ Φ₂} {Φ'} e e' s s' a a'  re = λ a0 a1 r → 
     rel-sub-cls {φ} {Φ₂} {Φ'} (e · a0) (e' · a1) s s' a a' 
    (re (a0 / ss ι a) (a1 / ss ι a') 
    (rel-cls-sub {φ} {Φ₁} {Φ'} a0 a1 s s' a a' r))

  rel-wk-cls : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧Γ (C A)  ⊢ ⟦ Φ ⟧Φ (C A)) 
         → (e' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R) 
         → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) 
         → (a : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ' ⟧Φ (C A)) → (a' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ' ⟧Φ R)
         → rel {φ} {Φ} e e' s s'
         → rel {φ , Φ'} {Φ} (wkTm vz e) (wkTm vz e') (cls s a) (cls s' a')
  rel-wk-cls {φ} {Φ} {Φ'} e e' s s' a a' re = rel-sub-cls {φ} {Φ} {Φ'} (wkTm vz e) (wkTm vz e') s s' a a' (≡rel {φ} {Φ} (sym (wkTm/sub vz e a)) (sym (wkTm/sub vz e' a')) refl refl re)

  rel-cls-sub : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧Γ (C A) , ⟦ Φ' ⟧Φ (C A) ⊢ ⟦ Φ ⟧Φ (C A)) 
            → (e' : ⟦ φ ⟧Γ R , ⟦ Φ' ⟧Φ R ⊢ ⟦ Φ ⟧Φ R) 
            → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) 
            → (a : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ' ⟧Φ (C A)) → (a' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ' ⟧Φ R)
            → rel {φ , Φ'} {Φ} e e' (cls s a) (cls s' a') 
            → rel {φ} {Φ} (e / sub vz a) (e' / sub vz a') s s'
  rel-cls-sub {φ} {Id} e e' s s' a a' re =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ □ %· %≡ merge-/ e (ss ι a) (↓-=> s) ⟩
     _ ⟷⟨ □ %· e -%/ ss (=>≡ (ι/=> (↓-=> s))) □ ⟩
     _ ⟷⟨ re ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (sym (ι/=> (↓-=> s')))) □ ⟩
     _ ⟷⟨ %≡ split-/ e' (ss ι a') (↓-=> s') ⟩
     _ ∎
  rel-cls-sub {φ} {K τ} e e' s s' a a' re =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ %≡ merge-/ e (ss ι a) (↓-=> s) ⟩
     _ ⟷⟨ e -%/ ss (=>≡ (ι/=> (↓-=> s))) □ ⟩
     _ ⟷⟨ re ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (sym (ι/=> (↓-=> s')))) □ ⟩
     _ ⟷⟨ %≡ split-/ e' (ss ι a') (↓-=> s') ⟩
     _ ∎
  rel-cls-sub {φ} {Φ₁ ⟶ Φ₂} {Φ'} e e' s s' a a' re = λ a0 a1 r → 
    ≡rel {φ} {Φ₂} (refl ≡· wkTm/sub vz a0 a) (refl ≡· wkTm/sub vz a1 a') refl refl
      (rel-cls-sub {φ} {Φ₂} {Φ'} _ _ s s' a a' 
      (re (wkTm vz a0) (wkTm vz a1) 
      (rel-wk-cls {φ} {Φ₁} {Φ'} a0 a1 s s' a a' r)))

rel-wk-cls' : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧Γ (C A)  ⊢ ⟦ Φ ⟧Φ (C A)) 
         → (e' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R) 
         → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) 
         → (a : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ' ⟧Φ (C A)) → (a' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ' ⟧Φ R)
         → rel {φ , Φ'} {Φ} (wkTm vz e) (wkTm vz e') (cls s a) (cls s' a')
         → rel {φ} {Φ} e e' s s'
rel-wk-cls' {φ} {Φ} {Φ'} e e' s s' a a' r = 
  ≡rel {φ} {Φ} (wkTm/sub vz e a) (wkTm/sub vz e' a') refl refl
 (rel-cls-sub {φ} {Φ} {Φ'} (wkTm vz e) (wkTm vz e') s s' a a' r)

rel-up : ∀ {φ Φ} → (e : ε ⊢ ⟦ Φ ⟧Φ (C A)) → (e' : ε ⊢ ⟦ Φ ⟧Φ R) 
       → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) 
       → rel {ε} {Φ} e e' ε ε
       → rel {φ} {Φ} (up e) (up e') s s'
rel-up {ε} {Φ} e e' ε ε r = ≡rel {ε} {Φ} (sym (/ι e)) (sym (/ι e')) refl refl r
rel-up {φ , Φ'} {Φ} e e' (cls y y') (cls y0 y1) r = rel-sub-cls {φ} {Φ} _ _ y y0 y' y1 (≡rel {φ} {Φ} (split-/ e sz _) (split-/ e' sz _) refl refl (rel-up {φ} {Φ} e e' y y0 r))

\end{code}