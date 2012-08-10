%if False
\begin{code}
{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --injective-type-constructors #-}

open import STLC public

module TTS (A : Ty) (R : Ty) (rep : ε ⊢ (A ⇒ R)) (abs : ε ⊢ (R ⇒ A)) where


open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
import Relation.Binary.EqReasoning

open import TTS.Functor public
open import TTS.Context public
\end{code}
%endif

\begin{code} 
data _∶_⊨_↝_ : (φ : Ftx) → (Φ : Functor) → ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A → ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R → Set where
  var   : ∀ {φ Φ} (v : φ ∋↝ Φ)
            → φ ∶ Φ ⊨ var (⟦ v ⟧∋ A) ↝ var (⟦ v ⟧∋ R)
  app   : ∀ {φ Φ₁ Φ₂ e₁ e₁' e₂ e₂'} 
             → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ e₁ ↝ e₁' → φ ∶ Φ₁ ⊨ e₂ ↝ e₂' 
             → φ ∶ Φ₂ ⊨ (e₁ · e₂) ↝ (e₁' · e₂')
  lam   : ∀ {φ Φ₁ Φ₂ e e'} → (φ , Φ₁) ∶ Φ₂ ⊨ e ↝ e' → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ Λ e ↝ Λ e'
  wk    : ∀ {φ Φ Φ'} 
          → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
          → φ ∶ Φ ⊨ e ↝ e' 
          → (φ , Φ') ∶ Φ ⊨ wkTm vz e ↝ wkTm vz e'
  i-rep : ∀ {φ e e'} → φ ∶ K A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ (up rep · e')
  i-abs : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ K A ⊨ e ↝ (up abs · e') 

θ' : ∀ {a b} → (ab : ε ⊢ a ⇒ b) → (re : ε ⊢ b ⇒ a) → (φ : Ftx) → ⟦ φ ⟧Γ a => ⟦ φ ⟧Γ b
θ' _ _ ε        = sz
θ' a r (y , y') = ss (wkS vz (θ' a r y)) (up (dimap y' · a · r) · var vz)

θ : (φ : Ftx) → ⟦ φ ⟧Γ R => ⟦ φ ⟧Γ A
θ = θ' abs rep

lookup-θ : ∀ {φ Φ} → (v : φ ∋↝ Φ) → lookup (⟦ v ⟧∋ R) (θ φ) ≡ (up (dimap Φ · abs · rep) · var (⟦ v ⟧∋ A))
lookup-θ vz     = refl
lookup-θ (vs {Γ} {Φ} y) = 
  let open ≡-Reasoning
  in begin
     _ ≡⟨ wk-lookup (⟦ y ⟧∋ R) vz (θ Γ) ⟩
     _ ≡⟨ cong (wkTm vz) (lookup-θ y) ⟩
     _ ∎

open import Data.Maybe
open import Data.Product
open import STLC.Congruence

*-id' : ∀ {Φ τ a b} → (p : just τ ≡ Φ *) → (ab : ε ⊢ b ⇒ a) → (re : ε ⊢ a ⇒ b)
     → dimap Φ · ab · re βη-≡ ! ε , ≡τrefl ⇒ *-eq≡τ {Φ} p >⊢ idε
*-id' {Φ} p ab re =
   let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
   in begin
      _ ⟷⟨ *-id {Φ} p %· int>⊢ %· int>⊢ ⟩
      _ ⟷⟨ cong-!>⊢ ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ} p) (Λ (Λ (Λ (var vz))) · ab · re) (Λ (var vz)) (β≡ brefl) ⟩
      _ ∎


θ'ι : ∀ {φ Γ a b} → {ab : ε ⊢ a ⇒ b} → {re : ε ⊢ b ⇒ a} 
   → (p : just Γ ≡ φ *Γ) → θ' {a} {b} ab re φ βη-=> ! ≡Γrefl , *Γ-eq p >=> ι
θ'ι {ε} p = sz
θ'ι {φ , Φ} p with *Γ-split {φ} {Φ} p
θ'ι {φ , Φ} {.(g , t)} {a} {b} p | g , t , eq , eq' , refl =
  let open Relation.Binary.EqReasoning βη=>setoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
   in begin
      _ ⟷⟨ cong-extS vz (cong-wkS vz (θ'ι eq)) (%up (*-id' {Φ} eq' _ _) %· □) ⟩
      _ ⟷⟨ cong-extS vz (=>sym (=>≡ (!,=>wkSvz ≡Γrefl _ (*-eq≡τ {Φ} {t} {a} eq') _))) (bsym (%≡ !,⊢up (*Γ-eq {φ} {g} {a} eq , ≡τrefl) (≡τrefl ⇒ *-eq≡τ {Φ} eq') (Λ (var vz))) %· %≡ cong var (sym (!,∋vz (*Γ-eq eq) ≡τrefl ≡τrefl))) ⟩
      _ ⟷⟨ cong-extS vz =>refl (cong-!>⊢ (*Γ-eq eq , ≡τrefl) (*-eq≡τ {Φ} eq') _ _ (id-id (var vz))) ⟩
      _  ⟷⟨ cong-extS vz =>refl (%≡ cong var (!,∋vz-flip (*Γ-eq eq) (*-eq≡τ {Φ} eq'))) ⟩
      _  ⟷⟨ cong-extS vz =>refl (%≡ cong (λ v' → ! (*Γ-eq {φ} {g} {a} eq , v') , ≡τrefl {⟦ Φ ⟧Φ a} >⊢ var vz) (≡τ-eq-eq _ _)) ⟩
      _ ∎

\end{code}
