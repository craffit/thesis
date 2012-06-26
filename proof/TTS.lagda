\begin{code}
{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --injective-type-constructors #-}
module TTS where

open import STLC.Eval
open import STLC.Prelude

-- open import Data.Unit

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
import Relation.Binary.EqReasoning
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
-- open Relation.Binary.EqReasoning βηsetoid renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _βη-≡⟨_⟩_)

open import STLC.Syntax
open import TTS.Functor
 
-- open Relation.Binary.EqReasoning ≡setoid renaming (begin to ≡begin ; ∎ to ≡∎)

module FunctorEnv where
  open Functor

  -- Functor context
  data Ftx : Set where
    ε : Ftx
    _▸_ : Ftx → Functor → Ftx

  ⟦_⟧Γ : Ftx → Ty → Con
  ⟦ ε ⟧Γ v = ε
  ⟦ φ ▸ Φ ⟧Γ v = ⟦ φ ⟧Γ v , ⟦ Φ ⟧Φ v

  -- Variable in functor context
  data CVar : Ftx → Functor → Set where
    vz : forall {φ Φ} → CVar (φ ▸ Φ) Φ
    vs : forall {Γ Φ₁ Φ₂} → CVar Γ Φ₁ → CVar (Γ ▸ Φ₂) Φ₁

  ⟦_⟧C : ∀ {φ Φ} → (v : CVar φ Φ) → (a : Ty) → Var (⟦ φ ⟧Γ a) (⟦ Φ ⟧Φ a)
  ⟦_⟧C vz t     = vz
  ⟦_⟧C (vs y) t = vs (⟦ y ⟧C t)

module TTS (A : Ty) (R : Ty) (rep : ε ⊢ (A ⇒ R)) (abs : ε ⊢ (R ⇒ A)) where
  open Functor
  open FunctorEnv

  data _∶_⊨_↝_ : (φ : Ftx) → (Φ : Functor) → ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A → ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R → Set where
    var   : ∀ {φ Φ} {v : CVar φ Φ}
              → φ ∶ Φ ⊨ var (⟦ v ⟧C A) ↝ var (⟦ v ⟧C R)
    app   : ∀ {φ Φ₁ Φ₂ e₁ e₁' e₂ e₂'} 
               → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ e₁ ↝ e₁' → φ ∶ Φ₁ ⊨ e₂ ↝ e₂' 
               → φ ∶ Φ₂ ⊨ (e₁ · e₂) ↝ (e₁' · e₂')
    lam   : ∀ {φ Φ₁ Φ₂ e e'} → (φ ▸ Φ₁) ∶ Φ₂ ⊨ e ↝ e' → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ Λ e ↝ Λ e'
    i-rep : ∀ {φ e e'} → φ ∶ K A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ (up rep · e')
    i-abs : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ K A ⊨ e ↝ (up abs · e')

  module Proof (rep-abs : (abs ∘ rep) βη-≡ id) where

    mutual
      data Nf : Con → Ty → Set where
        Λ   : forall {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
        ap  : forall {Γ τ} → Nf' Γ τ → Nf Γ τ
      
      data Nf' : Con → Ty → Set where
        var : forall {Γ σ} → Var Γ σ → Nf' Γ σ
        app : forall {Γ σ τ} → Nf' Γ (σ ⇒ τ) → Nf Γ σ → Nf' Γ τ


    _↓ : ∀ {Γ τ} → Γ ⊢ τ → Nf Γ τ
    v ↓ = {!!}
    
    ↓-βη : ∀ {Γ τ} → (a b : Γ ⊢ τ) → a ↓ ≡ b ↓ → a βη-≡ b
    ↓-βη a b p = {!!}

    
    abs-rep : ∀ {φ} → {e : ⟦ φ ⟧Γ A ⊢ A} → (e' : ⟦ φ ⟧Γ R ⊢ R) → (en : Nf (⟦ φ ⟧Γ R) R) → e' ↓ ≡ en → φ ∶ Id ⊨ e ↝ e' → (up rep · (up abs · e')) βη-≡ (id · e')
    abs-rep e' en p = {!en!}

    θ : (φ : Ftx) → ⟦ φ ⟧Γ R => ⟦ φ ⟧Γ A
    θ ε        = sz
    θ (y ▸ y') = ss (wkS vz (θ y)) (up (dimap y' · abs · rep) · var vz)

    lookup-θ : ∀ {φ Φ} → (v : CVar φ Φ) → lookup (⟦ v ⟧C R) (θ φ) ≡ (up (dimap Φ · abs · rep) · var (⟦ v ⟧C A))
    lookup-θ vz     = refl
    lookup-θ (vs {Γ} y) = 
      let open ≡-Reasoning
      in begin
         _ ≡⟨ wk-lookup (⟦ y ⟧C R) vz (θ Γ) ⟩
         _ ≡⟨ cong (λ v → wkTm vz v) (lookup-θ y) ⟩
         _ ∎

    mutual
{-
      abs-rep : ∀ {φ} → {e : ⟦ ε ⟧Γ A ⊢ A} {e' : ⟦ φ ⟧Γ R ⊢ R}  → φ ∶ Id ⊨ e ↝ e' → (up rep · (up abs · e')) βη-≡ (id · e')
      abs-rep var      = {!!}
      abs-rep (y · y') = {!!}
-}
      tts-prop : ∀ {φ Φ e e'} → φ ∶ Φ ⊨ e ↝ e' → ((up (dimap Φ · rep · abs) · e') / (θ φ)) βη-≡ e
      tts-prop (i-abs {φ} {e} {e'} y) =
          let open Relation.Binary.EqReasoning βηsetoid
               renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
          in begin
             _ ⟷⟨ bsym (do-comp (up (dimap (K A) · rep · abs)) (up abs) e') %/ θ φ ⟩
             _ ⟷⟨ ((%≡ up-app _ _ %· □) ⟷ %≡ up-app _ _ %· □' e') %/ θ φ ⟩
             _ ⟷⟨ (%up ((β≡ brefl) %∘ □) %· (□' e')) %/ θ φ ⟩
             _ ⟷⟨ (%up id-comp abs %· □' e') %/ θ φ ⟩
             _ ⟷⟨ (%up β≡ brefl %· □' e') %/ θ φ ⟩
             _ ⟷⟨ tts-prop y ⟩
             _ ∎

      tts-prop (i-rep {φ} {e} {e'} y) =
          let open Relation.Binary.EqReasoning βηsetoid
               renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
          in begin
              (up (dimap Id · rep · abs) · (up rep · e')) / θ φ
             ⟷⟨ (%up β≡ brefl %· (□' (up rep · e'))) %/ θ φ ⟩
              (up abs · (up rep · e')) / θ φ
             ⟷⟨ (bsym (do-comp (up abs) (up rep) e') ⟷ (up-comp _ _  ⟷ %up rep-abs %· □' e'))%/ θ φ ⟩
               (id · e') / θ φ
             ⟷⟨ (%up β≡ brefl %· □' e') %/ θ φ ⟩
               (up (dimap (K A) · rep · abs) · e') / θ φ
             ⟷⟨ tts-prop y ⟩
             _ ∎
             
      tts-prop (var {φ} {Φ} {v}) =
          let open Relation.Binary.EqReasoning βηsetoid
               renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
          in {!!} {-begin
             _ ⟷⟨ congApp (equiv (up/ (dimap Φ · rep · abs) (θ φ))) (equiv (lookup-θ v)) ⟩
             _ ⟷⟨ bsym (do-comp _ _ _) ⟩       
             _ ⟷⟨ (%≡ up-app _ _ %· □) ⟷ %≡ up-app _ _ ⟷ %up dimapcomp Φ _ _ _ _ %· □ ⟩
             _ ⟷⟨ %up ((□ %· rep-abs %· rep-abs) ⟷ dimapid Φ) %· □ ⟩
             _ ⟷⟨ (%≡ up-/sz id %· □) ⟷ beta ⟩
             _ ∎ -}
      tts-prop (app {φ} {Φ₁} {Φ₂} {e₁} {e₁'} {e₂} {e₂'} y y') =
          let open Relation.Binary.EqReasoning βηsetoid
               renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
          in {!!} {- begin
             _ ⟷⟨ congApp (equiv (up/ _ (θ φ))) brefl ⟩
             _ ⟷⟨ {!!} ⟩
             _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· (%up bsym (dimapcomp Φ₁ abs rep rep abs) %· □' e₂')) %/ θ φ ⟩
             _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· (bsym (up-comp (dimap Φ₁ · abs · rep) (dimap Φ₁ · rep · abs)) %· □' e₂')) %/ θ φ ⟩
             _ ⟷⟨ (□' (up (dimap Φ₂ · rep · abs) ∘ e₁') %· do-comp (up (dimap Φ₁ · abs · rep)) (up (dimap Φ₁ · rep · abs)) e₂') %/ θ φ ⟩
             _ ⟷⟨ bsym (do-comp (up (dimap Φ₂ · rep · abs) ∘ e₁') (up (dimap Φ₁ · abs · rep)) (up (dimap Φ₁ · rep · abs) · e₂')) %/ θ φ ⟩
             _ ⟷⟨ (bsym (do-dimap' {Φ₁} {Φ₂} rep abs e₁') %· □' (up (dimap Φ₁ · rep · abs) · e₂')) %/ θ φ ⟩
             _ ⟷⟨ tts-prop y %· tts-prop y' ⟩
             _ ∎ -}

      tts-prop (lam {φ} {Φ₁} {Φ₂} {e} {e'} y) =
          let open Relation.Binary.EqReasoning βηsetoid
               renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
          in {!!} {- begin 
             _ ⟷⟨ !up/ _ (θ φ) %· □ ⟩
             _ ⟷⟨ %up do-dimap {Φ₁} {Φ₂} rep abs %· □ ⟩
             _ ⟷⟨ %≡ up-/sz _ ⟷ %Λ (□ %· (□ %· %≡ wk-ext/ vz (dimap Φ₂ · rep · abs) _ _ ⟷ %≡ sym (up-/sz (dimap Φ₂ · rep · abs)) %· □) %· %≡ wk-ext/ vz (dimap Φ₁ · abs · rep) _ _ ⟷ %≡ sym (up-/sz (dimap Φ₁ · abs · rep))) %· □ ⟩
             _ ⟷⟨ beta ⟩
             _ ⟷⟨ □ %· (□ %· !up/ _ (ss ι _) %· □) %· !up/ _ (ss ι _) ⟩
             _ ⟷⟨ bsym eta ⟩
             _ ⟷⟨ %Λ (%≡ sym (up-/sz comp) %· (%≡ sym (up-/sz comp) %· □ %· □) %· □ %· □) ⟩
             _ ⟷⟨ %Λ (do-comp _ _ _ ⟷ do-comp _ _ _) ⟩
             _ ⟷⟨ %Λ (bsym (!up/ _ (ss (wkS vz (θ φ)) _)) %· beta ⟷ (%≡ wk-ext/ (vs vz) (e' / ss (wkS vz (θ φ)) (var vz)) (var vz) (ss (wkS vz ι) (app (wkTm vz (up (app (app (dimap Φ₁) abs) rep))) (var vz))) ⟷ (%≡ sym (wkS-ext/ (vs vz) e' (ss (wkS vz (θ φ)) (var vz)) (ss (wkS vz ι) (app (wkTm vz (up (app (app (dimap Φ₁) abs) rep))) (var vz))) (var vz)) ⟷ %≡ cong (λ p → (e' / ss p (var vz)) / ss (ss (wkS vz ι) (var vz)) (app (wkTm vz (up (app (app (dimap Φ₁) abs) rep))) (var vz))) (wkSExc vz vz (θ φ))) ⟷ %≡ sym (dist-sub vz e' vz (app (wkTm vz (up (app (app (dimap Φ₁) abs) rep))) (var vz)) _))) ⟩
             _ ⟷⟨ %Λ tts-prop y ⟩
             _ ∎ -}
{-             _ ⟷⟨ congApp (equiv (up/ _ (θ φ))) brefl ⟩
--             _ ⟷⟨ congApp (congUp (btrans (congApp beta brefl) beta)) brefl ⟩
             _ ⟷⟨ congApp (congUp (congApp beta brefl)) brefl ⟩
             _ ⟷⟨ congApp (congUp (congApp (congƛ (congƛ (congApp {!!} (congApp (congApp (equiv (up/ (dimap Φ₁) (wkSI vz vz (wkSI vz vz (ss sz rep))))) brefl) brefl)))) brefl)) brefl ⟩
             _ ⟷⟨ {!congApp!} ⟩
             _ ⟷⟨ congƛ (tts-prop y) ⟩
             
             _ ∎
-}

{-
      tts-prop {.(ε ▸ Φ)} {Φ} {ρ = env} var with env
      ... | ε ► r = 
            begin
              ⟦ dimap Φ · rep · abs ∘ dimap Φ · abs · rep ⟧ ε r
            ≡⟨ cong (λ v → v ε r) (dimapcomp Φ rep abs abs rep) ⟩
              ⟦ dimap Φ · (abs ∘ rep) · (abs ∘ rep) ⟧ ε r
            ≡⟨ cong₂ (λ v1 v2 → ⟦ dimap Φ ⟧ ε (v1 ε) (v2 ε) r) rep-abs rep-abs ⟩
              ⟦ dimap Φ · id · id ⟧ ε r
            ≡⟨ cong (λ v → v ε r) (dimapid Φ) ⟩
              r
            ∎
      tts-prop (y · y') = {!!}
      tts-prop {φ} {Φ₁ ⟶ Φ₂} {ƛ e1} {ƛ e2} {ρ} (lam y) =
         let prem : (λ x → ⟦ e1 ⟧ (ρ ► x)) ≡ (λ x → ⟦ up (dimap Φ₂ · rep · abs) · e2 ⟧ (θ (φ ▸ Φ₁) (ρ ► x)))
             prem = {!cong!}
         in begin
              ⟦ up (dimap (Φ₁ ⟶ Φ₂) · rep · abs) · ƛ e2 ⟧ (θ φ ρ)
            ≡⟨ {!!} ⟩
              (λ x → ⟦ up (dimap Φ₂ · rep · abs) · e2 ⟧ (θ (φ ▸ Φ₁) (ρ ► x)))
            ≡⟨ {!cong (\v → (\x → v)) (tts-prop {φ ▸ Φ₁} {Φ₂} {e1} {e2} {ρ ► x} y)!} ⟩
              (λ x → ⟦ e1 ⟧ (ρ ► x))
            ≡⟨ refl ⟩
              ⟦ ƛ e1 ⟧ ρ
            ∎
      -- tts-prop : ∀ {φ Φ e e'} {ρ : Env (⟦ φ ⟧Γ A)} → φ ∶ Φ ⊨ e ↝ e' → ⟦ up (dimap Φ · rep · abs) · e' ⟧ (θ φ ρ) ≡ ⟦ e ⟧ ρ
-}\end{code}
