\begin{code}

open import STLC

module TTS.Proof  (A : Ty) (R : Ty) (rep : ε ⊢ (A ⇒ R)) (abs : ε ⊢ (R ⇒ A)) where

import TTS
open TTS A R rep abs
open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
import Relation.Binary.EqReasoning

module Proof  (rep-abs : (abs ∘ rep) βη-≡ id) (abs-rep : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → e' βη-≡ up (rep ∘ abs) · e') where
  dimap-abs-rep : ∀ {φ Φ e e'} → φ ∶ Φ ⊨ e ↝ e' → up (dimap Φ · (rep ∘ abs) · (rep ∘ abs)) · e' βη-≡ e'
  dimap-abs-rep {φ} {Id} t =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ %≡ up-/sz _ %· □ ⟩
         _ ⟷⟨ beta %· □ %· □ ⟩
         _ ⟷⟨ beta %· □ ⟩
         _ ⟷⟨ bsym (%≡ up-/sz _) %· □ ⟩
         _ ⟷⟨ bsym (abs-rep t) ⟩
         _ ∎
  dimap-abs-rep {φ} {K τ} t = (%≡ up-/sz _ %· □) ⟷ (β≡ brefl)
  dimap-abs-rep {φ} {Φ₁ ⟶ Φ₂} {e} {e'} t =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ do-dimap' {Φ₁} {Φ₂} {R} {R} (rep ∘ abs) (rep ∘ abs) e' ⟩
         _ ⟷⟨ bsym eta ⟩
         _ ⟷⟨ %Λ do-comp _ _ _ ⟩
         _ ⟷⟨ %Λ (□ %· dimap-abs-rep {φ , Φ₁} {Φ₁} (TTS.var vz)) ⟩
         _ ⟷⟨ %Λ do-comp _ _ _ ⟩
         _ ⟷⟨ %Λ dimap-abs-rep {φ , Φ₁} {Φ₂} (TTS.app (TTS.wk t) (TTS.var vz)) ⟩
         _ ⟷⟨ eta ⟩
         _ ∎

  tts-prop : ∀ {φ Φ e e'} → φ ∶ Φ ⊨ e ↝ e' → ((up (dimap Φ · rep · abs) · e') / (θ φ)) βη-≡ e
  tts-prop (i-abs {φ} {e} {e'} y) =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ bsym (do-comp (up (dimap (K A) · rep · abs)) (up abs) e') %/ θ φ ⟩
         _ ⟷⟨ (up-comp (dimap (K A) · rep · abs) abs %· □' e') %/ θ φ ⟩
         _ ⟷⟨ (%up ((β≡ brefl) %∘ □) %· (□' e')) %/ θ φ ⟩
         _ ⟷⟨ (%up id-comp abs %· □' e') %/ θ φ ⟩
         _ ⟷⟨ (%up β≡ brefl %· □' e') %/ θ φ ⟩
         _ ⟷⟨ tts-prop y ⟩
         _ ∎

  tts-prop (i-rep {φ} {e} {e'} y) =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ (%up β≡ brefl %· (□' (up rep · e'))) %/ θ φ ⟩
         _ ⟷⟨ bsym (do-comp (up abs) (up rep) e') %/ θ φ ⟩
         _ ⟷⟨ (up-comp (up abs) (up rep) %· □' e') %/ θ φ ⟩  
         _ ⟷⟨ (%up rep-abs %· □' e') %/ θ φ ⟩
         _ ⟷⟨ (%up β≡ brefl %· □' e') %/ θ φ ⟩
         _ ⟷⟨ tts-prop y ⟩
         _ ∎
       
  tts-prop (var {φ} {Φ} v) =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ congApp (equiv (up/ (dimap Φ · rep · abs) (θ φ))) (equiv (lookup-θ v)) ⟩
         _ ⟷⟨ bsym (do-comp _ _ _) ⟩       
         _ ⟷⟨ up-comp _ _ %· □ ⟩
         _ ⟷⟨ %up dimapcomp Φ _ _ _ _ %· □ ⟩
         _ ⟷⟨ %up ((□ %· rep-abs %· rep-abs) ⟷ dimapid Φ) %· □ ⟩
         _ ⟷⟨ id-id _ ⟩
         _ ∎
  tts-prop (app {φ} {Φ₁} {Φ₂} {e₁} {e₁'} {e₂} {e₂'} y y') =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ bsym (do-comp (up (dimap Φ₂ · rep · abs)) e₁' e₂') %/ θ φ ⟩
         _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· bsym (dimap-abs-rep y')) %/ θ φ ⟩
         _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· (%up bsym (dimapcomp Φ₁ abs rep rep abs) %· □' e₂')) %/ θ φ ⟩
         _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· (bsym (up-comp (dimap Φ₁ · abs · rep) (dimap Φ₁ · rep · abs)) %· □' e₂')) %/ θ φ ⟩
         _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· do-comp (up (dimap Φ₁ · abs · rep)) (up (dimap Φ₁ · rep · abs)) e₂') %/ θ φ ⟩
         _ ⟷⟨ bsym (do-comp (up (dimap Φ₂ · rep · abs) ∘ e₁') (up (dimap Φ₁ · abs · rep)) (up (dimap Φ₁ · rep · abs) · e₂')) %/ θ φ ⟩
         _ ⟷⟨ (bsym (do-dimap' {Φ₁} {Φ₂} rep abs e₁') %· □' (up (dimap Φ₁ · rep · abs) · e₂')) %/ θ φ ⟩
         _ ⟷⟨ tts-prop y %· tts-prop y' ⟩
         _ ∎

  tts-prop (lam {φ} {Φ₁} {Φ₂} {e} {e'} y) =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin 
         _ ⟷⟨ !up/ _ (θ φ) %· □ ⟩
         _ ⟷⟨ %up do-dimap {Φ₁} {Φ₂} rep abs %· □ ⟩
         _ ⟷⟨ %≡ up-/sz _ ⟷ %Λ (□ %· (□ %· %≡ wk-ext/ vz (dimap Φ₂ · rep · abs) _ _ ⟷ %≡ sym (up-/sz (dimap Φ₂ · rep · abs)) %· □) %· %≡ wk-ext/ vz (dimap Φ₁ · abs · rep) _ _ ⟷ %≡ sym (up-/sz (dimap Φ₁ · abs · rep))) %· □ ⟩
         _ ⟷⟨ beta ⟩
         _ ⟷⟨ □ %· (□ %· !up/ _ (ss ι _) %· □) %· !up/ _ (ss ι _) ⟩
         _ ⟷⟨ bsym eta ⟩
         _ ⟷⟨ %Λ (%≡ sym (up-/sz comp) %· (%≡ sym (up-/sz comp) %· □ %· □) %· □ %· □) ⟩
         _ ⟷⟨ %Λ (do-comp _ _ _ ⟷ do-comp _ _ _) ⟩
         _ ⟷⟨ %Λ (bsym (!up/ _ (ss (wkS vz (θ φ)) _)) %· beta) ⟩
         _ ⟷⟨ %Λ (□ %· (%≡ wk-ext/ (vs vz) (e' / ss (wkS vz (θ φ)) (var vz)) (var vz) (ss (wkS vz ι) (wkTm vz (up (dimap Φ₁ · abs · rep)) · var vz)))) ⟩
         _ ⟷⟨ %Λ (□ %· (%≡ sym (wkS-ext/ (vs vz) e' (ss (wkS vz (θ φ)) (var vz)) (ss (wkS vz ι) (wkTm vz (up (dimap Φ₁ · abs · rep)) · var vz)) (var vz)))) ⟩
         _ ⟷⟨ %Λ (□ %· (%≡ cong (λ p → (e' / ss p (var vz)) / ss (ss (wkS vz ι) (var vz)) (wkTm vz (up (dimap Φ₁ · abs · rep)) · var vz)) (wkSExc vz vz (θ φ)))) ⟩
         _ ⟷⟨ %Λ (□ %· (%≡ sym (dist-sub vz e' vz (wkTm vz (up (dimap Φ₁ · abs · rep)) · var vz) _))) ⟩
         _ ⟷⟨ %Λ tts-prop y ⟩
         _ ∎
  tts-prop (wk {φ} {Φ} {Φ'} {e} {e'} t) = 
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in begin
         _ ⟷⟨ %≡ wk-ext/ vz (up (dimap Φ · rep · abs) · e') _ _ ⟩
         _ ⟷⟨ %≡ wk/ vz (up (dimap Φ · rep · abs) · e') _ ⟩
         _ ⟷⟨ %wkTm vz (tts-prop t) ⟩
         _ ∎  
  open import Data.Maybe

  !* : ∀ {φ Φ Γ τ} → (p : just Γ ≡ φ *Γ) → (p' : just τ ≡ Φ *) 
          → {a : Ty} → (e : ⟦ φ ⟧Γ a ⊢ ⟦ Φ ⟧Φ a) → Γ ⊢ τ
  !* {φ} {Φ} p1 p2 e = ! *Γ-Con {φ} p1 , *-≡τ {Φ} p2 >⊢ e

  tts-eq' : ∀ {φ Φ Γ τ} → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R} 
         → φ ∶ Φ ⊨ e ↝ e' → (p : just Γ ≡ φ *Γ) → (p' : just τ ≡ Φ *) 
         → e βη-≡ ! *Γ-eq {φ} p , *-eq≡τ {Φ} p' >⊢ e'
  tts-eq' {φ} {Φ} {Γ} {τ} {e} {e'} t p p' =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in  begin
          _ ⟷⟨ bsym (tts-prop t) ⟩
          _ ⟷⟨ cong/s (θ'ι p) (up (dimap Φ · rep · abs) · e') ⟩
          _ ⟷⟨ cong/ {t = (up (dimap Φ · rep · abs) · e')} (%up_ {⟦ φ ⟧Γ R} (*-id' {Φ} p' rep abs) %· □) (! ≡Γrefl , *Γ-eq {φ} p >=> ι) ⟩
          _ ⟷⟨ %≡ !,⊢/ ≡Γrefl (*Γ-eq {φ} p) ι (up (! ε , ≡τrefl ⇒ *-eq≡τ {Φ} p' >⊢ idε) · e') ⟩
          _ ⟷⟨ cong-!>⊢ (*Γ-eq {φ} p) ≡τrefl _ _ (cong/ (%≡ !,⊢-id (≡Γsym ≡Γrefl) ≡τrefl (up (! ε , ≡τrefl ⇒ *-eq≡τ {Φ} p' >⊢ idε) · e')) ι) ⟩
          _ ⟷⟨ cong-!>⊢ (*Γ-eq {φ} p) ≡τrefl _ _ (%≡ /ι (up (! ε , ≡τrefl ⇒ *-eq≡τ {Φ} p' >⊢ idε) · e')) ⟩
          _ ⟷⟨ cong-!>⊢ (*Γ-eq {φ} p) ≡τrefl _ _ (bsym (%≡ !,⊢up ≡Γrefl _ (Λ (var vz))) %· int>⊢) ⟩
          _ ⟷⟨ cong-!>⊢ (*Γ-eq {φ} p) ≡τrefl _ _ (cong-!>⊢ ≡Γrefl (*-eq≡τ {Φ} p') _ _ (id-id e')) ⟩
          _ ⟷⟨ %≡ !,⊢-comm-trans _ _ _ _ _ ⟩
          _ ⟷⟨ %≡ cong₂ (λ v' v0 → ! v' , v0 >⊢ e') (≡Γ-eq-eq _ _) (≡τ-eq-eq _ _) ⟩
          _ ∎

  tts-eq : ∀ {φ Φ Γ τ} → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R} 
         → φ ∶ Φ ⊨ e ↝ e' → (p : just Γ ≡ φ *Γ) → (p' : just τ ≡ Φ *) 
         → !* {φ} {Φ} {Γ} {τ} p p' e βη-≡ !* {φ} {Φ} {Γ} {τ} p p' e'
  tts-eq {e' = e'} p p' t =
      let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
      in  begin
          _ ⟷⟨ cong-!>⊢ _ _ _ _ (tts-eq' p p' t) ⟩
          _ ⟷⟨ %≡ !,⊢-comm-trans _ _ _ _ _ ⟩
          _ ⟷⟨ %≡ cong₂ (λ v' v0 → ! v' , v0 >⊢ e') (≡Γ-eq-eq _ _) (≡τ-eq-eq _ _) ⟩
          _ ∎

\end{code}