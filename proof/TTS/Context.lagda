%if False
\begin{code}
module TTS.Context where

open import STLC
open import TTS.Functor

infix 4 _∋↝_
infixl 5 _-↝_

\end{code}
%endif

\begin{code}
data Ftx : Set where
  ε    : Ftx
  _,_  : Ftx → Functor → Ftx

⟦_⟧Γ : Ftx → Ty → Con
⟦ ε      ⟧Γ v = ε
⟦ φ , Φ  ⟧Γ v = ⟦ φ ⟧Γ v , ⟦ Φ ⟧Φ v
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
_-↝_ : {Φ : Functor} → (φ : Ftx) → φ ∋↝ Φ → Ftx
ε       -↝ ()
(φ , Φ) -↝ vz     = φ
(φ , Φ) -↝ (vs x) = (φ -↝ x) , Φ

wkv↝ : ∀ {φ Φ Φ'} → (x : φ ∋↝ Φ') → φ -↝ x ∋↝ Φ → φ ∋↝ Φ
wkv↝ vz     y       = vs y
wkv↝ (vs x) vz      = vz
wkv↝ (vs x) (vs y)  = vs (wkv↝ x y)

open import Relation.Binary.PropositionalEquality

substV-eq : ∀ {φ Φ τ} → (x : φ ∋↝ Φ) → ⟦ φ -↝ x ⟧Γ τ ≡ ⟦ φ ⟧Γ τ - ⟦ x ⟧∋ τ
substV-eq vz = refl
substV-eq {φ , Φ₂} {Φ} {τ} (vs y) = cong (λ v' → v' , ⟦ Φ₂ ⟧Φ τ) (substV-eq y)
\end{code}