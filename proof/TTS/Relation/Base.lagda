{-# OPTIONS --termination-depth=20 #-}
\begin{code}

open import STLC

module TTS.Relation.Base  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

open import TTS.Functor.Base
open import TTS.Context.Base
open import Util.PropositionalEquality

rel : ∀ {φ Φ} → (e : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)) → (e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R)
    → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) → Set
rel {φ} {Id}       e e' s s' = up rep · close e s βη-≡ close e' s' 
rel {φ} {K τ}      e e' s s' = close e s βη-≡ close e' s' 
rel {φ} {Φ₁ ⟶ Φ₂} e e' s s' = ∀ a a' → rel {φ} {Φ₁} a a' s s' → rel {φ} {Φ₂} (e · a) (e' · a') s s'

data Rel↓ : (φ : Ftx)  → (⟦ φ ⟧Γ (C A) ↓) → (⟦ φ ⟧Γ R ↓) → Set where
  ε   : Rel↓ ε ε ε
  cls : ∀ {φ Φ} {e : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)} {e' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
        → {s : ⟦ φ ⟧Γ (C A) ↓} → {s' : ⟦ φ ⟧Γ R ↓} → Rel↓ φ s s' 
        → rel {φ} {Φ} e e' s s' → Rel↓ (φ , Φ) (cls s e) (cls s' e')

data Rel=> (φ' : Ftx) (s : ⟦ φ' ⟧Γ (C A) ↓) (s' : ⟦ φ' ⟧Γ R ↓) : 
           (φ : Ftx) → (⟦ φ ⟧Γ (C A) => ⟦ φ' ⟧Γ (C A)) → (⟦ φ ⟧Γ R => ⟦ φ' ⟧Γ R)
           → Set where
  ε   : Rel=> φ' s s' ε sz sz
  ss : ∀ {φ Φ} {e : ⟦ φ' ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)} {e' : ⟦ φ' ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
         {t : ⟦ φ ⟧Γ (C A) => ⟦ φ' ⟧Γ (C A)} {t' : ⟦ φ ⟧Γ R => ⟦ φ' ⟧Γ R} 
        → Rel=> φ' s s' φ t t' → rel {φ'} {Φ} e e' s s' 
        → Rel=> φ' s s' (φ , Φ) (ss t e) (ss t' e')

≡rel : ∀ {φ Φ} {e e' : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)} {f f' : ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
     {s s' : ⟦ φ ⟧Γ (C A) ↓} {t t' : ⟦ φ ⟧Γ R ↓} → e ≡ e' → f ≡ f' → s ≡ s'
     → t ≡ t' → rel {φ} {Φ} e f s t → rel {φ} {Φ} e' f' s' t'
≡rel refl refl refl refl v = v

rel-βη : ∀ {φ Φ} {e e' : ⟦ φ ⟧Γ (C A) ⊢ ⟦ Φ ⟧Φ (C A)} {f f' :  ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R}
         → (s : ⟦ φ ⟧Γ (C A) ↓) → (s' : ⟦ φ ⟧Γ R ↓) → e βη-≡ e' → f βη-≡ f' 
         → rel {φ} {Φ} e f s s' → rel {φ} {Φ} e' f' s s'
rel-βη {φ} {Id} s s' eq1 eq2 r = (□ %· %close s (bsym eq1)) ⟷ r ⟷ %close s' eq2
rel-βη {φ} {K τ} s s' eq1 eq2 r =  %close s (bsym eq1) ⟷ r ⟷ %close s' eq2
rel-βη {φ} {Φ₁ ⟶ Φ₂} s s' eq1 eq2 r = λ a a' ra → rel-βη {φ} {Φ₂} s s' (eq1 %· □) (eq2 %· □) (r a a' ra)
                                         
\end{code}