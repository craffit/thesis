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
  wk    : ∀ {φ Φ Φ'} → (v : φ ∋↝ Φ') 
            → {e : ⟦ φ -↝ v ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ -↝ v ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
            → (φ -↝ v) ∶ Φ ⊨ e ↝ e' 
            → φ ∶ Φ ⊨ wkTm (⟦ v ⟧∋ A) (! substV-eq v >₁ e) ↝ wkTm (⟦ v ⟧∋ R) (! substV-eq v >₁ e')
  i-rep : ∀ {φ e e'} → φ ∶ K A ⊨ e ↝ e' → φ ∶ Id ⊨ e ↝ (up rep · e')
  i-abs : ∀ {φ e e'} → φ ∶ Id ⊨ e ↝ e' → φ ∶ K A ⊨ e ↝ (up abs · e')

!_↝_>↝_ : ∀ {φ Φ e e' ec ec'} → e ≡ ec → e' ≡ ec' → φ ∶ Φ ⊨ e ↝ e' → φ ∶ Φ ⊨ ec ↝ ec'
! refl ↝ refl >↝ t = t 
 
open ≡-Reasoning
{-
wk↝ : ∀ {φ Φ Φ'} → (x : φ ∋↝ Φ') 
    → {e : ⟦ φ -↝ x ⟧Γ A ⊢ ⟦ Φ ⟧Φ A} → {e' : ⟦ φ -↝ x ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
    → (φ -↝ x) ∶ Φ ⊨ e ↝ e' 
    → φ ∶ Φ ⊨ wkTm (⟦ x ⟧∋ A) (! substV-eq x >₁ e) ↝ wkTm (⟦ x ⟧∋ R) (! substV-eq x >₁ e')
wk↝ x (var v) = ! {!sym (cong (wkTm (⟦ x ⟧∋ A)) (!var (substV-eq x) (⟦ v ⟧∋ A)))!} ↝ {!!} >↝ var (wkv↝ x v)
wk↝ x (app y y') = ! sym (cong (wkTm _) (!· (substV-eq x) _ _)) ↝ sym (cong (wkTm _) (!· (substV-eq x) _ _)) >↝ app (wk↝ x y) (wk↝ x y')
wk↝ x (lam y) = {!lam ?!}
wk↝ {φ} x (i-rep {.(φ -↝ x)} {e} {e'} y) = ! refl ↝ (begin _ ≡⟨ {!!} ⟩ _ ≡⟨ cong (λ v' → wkTm _ v' · wkTm (⟦ x ⟧∋ R) (! substV-eq x >₁ e')) (sym (!up (substV-eq x) rep)) ⟩ _ ≡⟨ refl ⟩ _ ≡⟨ cong (wkTm _) (sym (!· (substV-eq x) {!!} {!!})) ⟩ _ ∎) >↝ i-rep (wk↝ x y)
wk↝ x (i-abs y) = {!!}
-}

θ : (φ : Ftx) → ⟦ φ ⟧Γ R => ⟦ φ ⟧Γ A
θ ε        = sz
θ (y , y') = ss (wkS vz (θ y)) (up (dimap y' · abs · rep) · var vz)

lookup-θ : ∀ {φ Φ} → (v : φ ∋↝ Φ) → lookup (⟦ v ⟧∋ R) (θ φ) ≡ (up (dimap Φ · abs · rep) · var (⟦ v ⟧∋ A))
lookup-θ vz     = refl
lookup-θ (vs {Γ} {Φ} y) = 
  let open ≡-Reasoning
  in begin
     _ ≡⟨ wk-lookup (⟦ y ⟧∋ R) vz (θ Γ) ⟩
     _ ≡⟨ cong (wkTm vz) (lookup-θ y) ⟩
     _ ∎


\end{code}
