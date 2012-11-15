%if False
\begin{code}
module TTS.Context.Base where

open import STLC
open import TTS.Functor.Base
open import Util.PropositionalEquality

infix 4 _∋↝_
infixl 5 _-↝_

\end{code}
%endif

\begin{code}
data Ftx : Set where
  ε    : Ftx
  _,_  : (φ : Ftx) → (Φ : Functor) → Ftx

⟦_⟧Γ : Ftx → Ty → Con
⟦ ε      ⟧Γ n = ε
⟦ φ , Φ  ⟧Γ n = ⟦ φ ⟧Γ n , ⟦ Φ ⟧Φ n
\end{code}


\begin{code}
data _∋↝_ : Ftx → Functor → Set where
  vz : ∀ {φ Φ} → φ , Φ ∋↝ Φ
  vs : ∀ {Γ Φ₁ Φ₂} → Γ ∋↝ Φ₁ → Γ , Φ₂ ∋↝ Φ₁

⟦_⟧∋ : ∀ {φ Φ} → (v : φ ∋↝ Φ) → (a : Ty) → ⟦ φ ⟧Γ a ∋ ⟦ Φ ⟧Φ a
⟦ vz    ⟧∋ t = vz
⟦ vs y  ⟧∋ t = vs (⟦ y ⟧∋ t)    
\end{code}

\begin{code}
_↑φ : Con → Ftx
ε ↑φ = ε
(y , y') ↑φ = y ↑φ , (y' ↑Φ)

↑φ-≡Γ : ∀ {a Γ} → Γ ≡Γ ⟦ Γ ↑φ ⟧Γ a
↑φ-≡Γ {a} {ε} = ε
↑φ-≡Γ {a} {y , y'} = ↑φ-≡Γ , ↑Φ-≡τ

\end{code}

\begin{code}
{-
data _↓φ : Ftx → Set where
  ε   : ε ↓φ
  _,_ : ∀ {φ Φ} → φ ↓φ → Φ ↓Φ → (φ , Φ) ↓φ

_↓τ : ∀ {Φ} → Φ ↓Φ → Ty
(C n) ↓τ     = C n
(y ⟶ y') ↓τ = y ↓τ ⇒ y' ↓τ

↓Φ-≡τ : ∀ {a Φ} {v : Φ ↓Φ} → v ↓τ ≡τ ⟦ Φ ⟧Φ a
↓Φ-≡τ {a} {Id} {()}
↓Φ-≡τ {a} {K .y} {C y} = C y
↓Φ-≡τ {a} {Φ₁ ⟶ Φ₂} {v ⟶ v'} = ↓Φ-≡τ ⇒ ↓Φ-≡τ
-}
\end{code}

\begin{code}
_-↝_ : {Φ : Functor} → (φ : Ftx) → φ ∋↝ Φ → Ftx
ε       -↝ ()
(φ , Φ) -↝ vz     = φ
(φ , Φ) -↝ (vs x) = (φ -↝ x) , Φ

wkv∋↝ : ∀ {φ Φ Φ'} → (x : φ ∋↝ Φ') → φ -↝ x ∋↝ Φ → φ ∋↝ Φ
wkv∋↝ vz     y       = vs y
wkv∋↝ (vs x) vz      = vz
wkv∋↝ (vs x) (vs y)  = vs (wkv∋↝ x y)

{-
-↝dist≡ :  ∀ {φ Φ} → (x : φ ∋↝ Φ) → Ty → Set
-↝dist≡ {φ} x τ = ⟦ φ -↝ x ⟧Γ τ ≡Γ ⟦ φ ⟧Γ τ - ⟦ x ⟧∋ τ

substV-eq : ∀ {φ Φ τ} → (x : φ ∋↝ Φ) → -↝dist≡ x τ
substV-eq vz = ≡Γrefl
substV-eq {φ , Φ₂} {Φ} {τ} (vs y) = substV-eq y , ≡τrefl

wkTm↝ : ∀ {φ Φ τ σ} → (x : φ ∋↝ Φ) → ⟦ φ -↝ x ⟧Γ τ ⊢ σ → ⟦ φ ⟧Γ τ ⊢ σ
wkTm↝ {τ = τ} x t = wkTm (⟦ x ⟧∋ τ) (! substV-eq x , ≡τrefl >⊢ t)

wkv↝ : ∀ {φ Φ τ σ} → (x : φ ∋↝ Φ) → ⟦ φ -↝ x ⟧Γ τ ∋ σ → ⟦ φ ⟧Γ τ ∋ σ
wkv↝ {τ = τ} x t = wkv (⟦ x ⟧∋ τ) (! substV-eq x , ≡τrefl >∋ t)

wkv∋↝-eq : ∀ {φ Φ Φ' a} → (v : φ ∋↝ Φ') → (v' : φ -↝ v ∋↝ Φ)
     → ⟦ wkv∋↝ v v' ⟧∋ a ≡ wkv (⟦ v ⟧∋ a) (! substV-eq v , ≡τrefl >∋ ⟦ v' ⟧∋ a)
wkv∋↝-eq vz v' = cong vs (sym (!,∋-id ≡Γrefl ≡τrefl (⟦ v' ⟧∋ _)))
wkv∋↝-eq (vs y) vz = cong (wkv (vs (⟦ y ⟧∋ _))) (sym (!,∋vz (substV-eq y) ≡τrefl ≡τrefl))
wkv∋↝-eq (vs y) (vs y') = cong vs (wkv∋↝-eq y y')
-}
\end{code}