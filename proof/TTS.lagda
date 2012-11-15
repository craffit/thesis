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
{-  wk    : ∀ {φ Φ Φ'} 
          → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
          → φ ∶ Φ ⊨ e ↝ e' 
          → (φ , Φ') ∶ Φ ⊨ wkTm vz e ↝ wkTm vz e'
-}
  split-K : ∀ {φ τ σ e e'} → φ ∶ K (σ ⇒ τ) ⊨ e ↝ e' 
          → φ ∶ K σ ⟶ K τ ⊨ e ↝ e'
  merge-K : ∀ {φ τ σ e e'} → φ ∶ K σ ⟶ K τ ⊨ e ↝ e' 
          → φ ∶ K (σ ⇒ τ) ⊨ e ↝ e'
  i-rep : ∀ {φ e e'} → φ ∶ K A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ (up rep · e')
  i-abs : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ K A ⊨ e ↝ (up abs · e') 
{-
wkTm⊨ : ∀ {φ Φ Φ'} → (v : φ ∋↝ Φ') → ∀ {e e'} → (φ -↝ v) ∶ Φ ⊨ e ↝ e' → φ ∶ Φ ⊨ wkTm↝ v e ↝ wkTm↝ v e'
wkTm⊨ {φ} {Φ} v (var v') = subst₂ (λ eq1 eq2 → φ ∶ Φ ⊨ var eq1 ↝ var eq2) (wkv∋↝-eq v v') (wkv∋↝-eq v v') (var (wkv∋↝ v v'))
wkTm⊨ v (app y y') = app (wkTm⊨ v y) (wkTm⊨ v y')
wkTm⊨ v (lam y)    = lam (wkTm⊨ (vs v) y)
wkTm⊨ {φ} v (i-rep {e = e} {e' = e'} y)  = ≡subst 
      (\eq → 
      φ ∶ Id ⊨ wkTm (⟦ v ⟧∋ A) (! substV-eq v , ≡τrefl >⊢ e) ↝
      (eq · wkTm (⟦ v ⟧∋ R) (! substV-eq v , ≡τrefl >⊢ e'))) 
      ( let open ≡-Reasoning
        in begin
           _ ≡⟨ sym (wk-up (⟦ v ⟧∋ R) rep) ⟩
           _ ≡⟨ cong (wkTm (⟦ v ⟧∋ R))
                  (sym (cong (λ v' → up v') (!,⊢-id ε ≡τrefl rep))) ⟩
           _ ≡⟨ cong (wkTm (⟦ v ⟧∋ R))
                  (sym (!,⊢up (substV-eq v) (≡τrefl ⇒ ≡τrefl) rep)) ⟩
           _ ∎
      )
      (i-rep (wkTm⊨ v y))
wkTm⊨ {φ} v (i-abs {e = e} {e' = e'} y)  =  ≡subst 
      (\eq → 
      φ ∶ K A ⊨ wkTm (⟦ v ⟧∋ A) (! substV-eq v , ≡τrefl >⊢ e) ↝
      (eq · wkTm (⟦ v ⟧∋ R) (! substV-eq v , ≡τrefl >⊢ e'))) 
      ( let open ≡-Reasoning
        in begin
           _ ≡⟨ sym (wk-up (⟦ v ⟧∋ R) abs) ⟩
           _ ≡⟨ cong (wkTm (⟦ v ⟧∋ R))
                  (sym (cong (λ v' → up v') (!,⊢-id ε ≡τrefl abs))) ⟩
           _ ≡⟨ cong (wkTm (⟦ v ⟧∋ R))
                  (sym (!,⊢up (substV-eq v) (≡τrefl ⇒ ≡τrefl) abs)) ⟩
           _ ∎
      )
      (i-abs (wkTm⊨ v y))

wkTmvz⊨ : ∀ {φ Φ Φ'} → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
          → φ ∶ Φ ⊨ e ↝ e' → (φ , Φ') ∶ Φ ⊨ wkTm vz e ↝ wkTm vz e'
wkTmvz⊨ {φ} {Φ} {Φ'} {e} {e'} v = subst₂ (λ eq' eq0 → (φ , Φ') ∶ Φ ⊨ wkTm vz eq' ↝ wkTm vz eq0) (!,⊢-id ≡Γrefl ≡τrefl e) (!,⊢-id ≡Γrefl ≡τrefl e') (wkTm⊨ vz v)

eta⊨ : ∀ {φ Φ Φ'} → {e : ⟦ φ ⟧Γ A ⊢ ⟦ Φ' ⟶ Φ ⟧Φ A} 
     → {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ' ⟶ Φ ⟧Φ R} → φ ∶ Φ' ⟶ Φ ⊨ e ↝ e' 
     → φ ∶ Φ' ⟶ Φ ⊨ Λ (wkTm vz e · var vz) ↝ Λ (wkTm vz e' · var vz)
eta⊨ p = lam (app (wkTmvz⊨ p) (var vz))
-}

θ' : ∀ {a b} → (ab : ε ⊢ a ⇒ b) → (re : ε ⊢ b ⇒ a) → (φ : Ftx) → ⟦ φ ⟧Γ a => ⟦ φ ⟧Γ b
θ' _ _ ε        = sz
θ' a r (y , y') = ss (wkS vz (θ' a r y)) (up (dimap y' · a · r) · var vz)

θ'-K : ∀ {a b σ} → (ab : ε ⊢ a ⇒ b) → (re : ε ⊢ b ⇒ a) → (φ : Ftx)
     → ss (wkS vz (θ' ab re φ)) (var vz) βη-=> θ' ab re (φ , K σ)
θ'-K ab re φ = ss =>refl (bsym (dimap-const ab re (var vz)))

θ : (φ : Ftx) → ⟦ φ ⟧Γ R => ⟦ φ ⟧Γ A
θ = θ' abs rep

lookup-θ' : ∀ {φ Φ a b} → (ab : ε ⊢ a ⇒ b) → (re : ε ⊢ b ⇒ a)→ (v : φ ∋↝ Φ) → lookup (⟦ v ⟧∋ a) (θ' ab re φ) ≡ (up (dimap Φ · ab · re) · var (⟦ v ⟧∋ b))
lookup-θ' ab re vz     = refl
lookup-θ' {a = a} ab re (vs {Γ} {Φ} y) = 
  let open ≡-Reasoning
  in begin
     _ ≡⟨ wk-lookup (⟦ y ⟧∋ a) vz (θ' ab re Γ) ⟩
     _ ≡⟨ cong (wkTm vz) (lookup-θ' ab re  y) ⟩
     _ ∎

open import Data.Maybe
open import Data.Product
open import STLC.Congruence
{-
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
      _ ⟷⟨ cong-extS vz =>refl (cong-!>⊢ (*Γ-eq eq , ≡τrefl) (*-eq≡τ {Φ} eq') _ _ (up-id-id (var vz))) ⟩
      _  ⟷⟨ cong-extS vz =>refl (%≡ cong var (!,∋vz-flip (*Γ-eq eq) (*-eq≡τ {Φ} eq'))) ⟩
      _  ⟷⟨ cong-extS vz =>refl (%≡ cong (λ v' → ! (*Γ-eq {φ} {g} {a} eq , v') , ≡τrefl {⟦ Φ ⟧Φ a} >⊢ var vz) (≡τ-eq-eq _ _)) ⟩
      _ ∎
-}
\end{code}
