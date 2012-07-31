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
         _ ⟷⟨ %Λ dimap-abs-rep {φ , Φ₁} {Φ₂} (TTS.app (TTS.wk vz t) (TTS.var vz)) ⟩
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
         _ ⟷⟨ %Λ (bsym (!up/ _ (ss (wkS vz (θ φ)) _)) %· beta ⟷ (%≡ wk-ext/ (vs vz) (e' / ss (wkS vz (θ φ)) (var vz)) (var vz) (ss (wkS vz ι) (wkTm vz (up (dimap Φ₁ · abs · rep)) · var vz)) ⟷ (%≡ sym (wkS-ext/ (vs vz) e' (ss (wkS vz (θ φ)) (var vz)) (ss (wkS vz ι) (_·_ (wkTm vz (up (_·_ (_·_ (dimap Φ₁) abs) rep))) (var vz))) (var vz)) ⟷ %≡ cong (λ p → (e' / ss p (var vz)) / ss (ss (wkS vz ι) (var vz)) (_·_ (wkTm vz (up (_·_ (_·_ (dimap Φ₁) abs) rep))) (var vz))) (wkSExc vz vz (θ φ))) ⟷ %≡ sym (dist-sub vz e' vz (_·_ (wkTm vz (up (_·_ (_·_ (dimap Φ₁) abs) rep))) (var vz)) _))) ⟩
         _ ⟷⟨ %Λ tts-prop y ⟩
         _ ∎ 
  tts-prop (wk v t) = {!!}
\end{code}