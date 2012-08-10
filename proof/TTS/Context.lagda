%if False
\begin{code}
module TTS.Context where

open import STLC
open import TTS.Functor

open import Data.Maybe
open import Category.Monad
open import STLC.Congruence

open import Relation.Binary.PropositionalEquality
open import Data.Product

infix 4 _∋↝_
infixl 5 _-↝_

\end{code}
%endif

\begin{code}
data Ftx : Set where
  ε    : Ftx
  _,_  : (φ : Ftx) → (Φ : Functor) → Ftx

⟦_⟧Γ : Ftx → Ty → Con
⟦ ε      ⟧Γ v = ε
⟦ φ , Φ  ⟧Γ v = ⟦ φ ⟧Γ v , ⟦ Φ ⟧Φ v
\end{code}

\begin{code}
_*Γ : Ftx → Maybe Con
ε *Γ = just ε
(φ , Φ) *Γ =
  let open RawMonadPlus monadPlus
  in _,_ <$> φ *Γ ⊛ Φ *

*Γ-split : ∀ {φ Φ Γ} → just Γ ≡ (φ , Φ) *Γ 
      → Σ Con (\g → Σ Ty (\τ → (just g ≡ φ *Γ) × (just τ ≡ Φ *) × (Γ ≡ g , τ)))
*Γ-split {φ} {Φ} p with φ *Γ | Φ *
*Γ-split refl | just x | just x' = x , (x' , (refl , (refl , refl)))
*Γ-split () | just x | nothing
*Γ-split () | nothing | r2 

*Γ-Con : ∀ {φ Γ σ} → just Γ ≡ φ *Γ → ⟦ φ ⟧Γ σ ≡Γ Γ
*Γ-Con {ε} refl = ε
*Γ-Con {φ , Φ} p with *Γ-split {φ} {Φ} p
*Γ-Con {φ , Φ} {.(x , x')} {a} p | x , (x' , (eq , (eq' , refl))) = *Γ-Con eq , *-≡τ {Φ} {x'} {a} eq'

*Γ-eq : ∀ {φ Γ a b} → just Γ ≡ φ *Γ → ⟦ φ ⟧Γ a ≡Γ ⟦ φ ⟧Γ b
*Γ-eq {φ} {Γ} {a} {b} p = ≡Γtrans (*Γ-Con {φ} {Γ} {a} p) (≡Γsym (*Γ-Con {φ} {Γ} {b} p))

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

-↝dist≡ :  ∀ {φ Φ} → (x : φ ∋↝ Φ) → Ty → Set
-↝dist≡ {φ} x τ = ⟦ φ -↝ x ⟧Γ τ ≡ ⟦ φ ⟧Γ τ - ⟦ x ⟧∋ τ

substV-eq : ∀ {φ Φ τ} → (x : φ ∋↝ Φ) → -↝dist≡ x τ
substV-eq vz = refl
substV-eq {φ , Φ₂} {Φ} {τ} (vs y) = cong (λ v' → v' , ⟦ Φ₂ ⟧Φ τ) (substV-eq y)

wkTm↝ : ∀ {φ Φ Φ' τ} → (x : φ ∋↝ Φ') → ⟦ φ -↝ x ⟧Γ τ ⊢ ⟦ Φ ⟧Φ τ → ⟦ φ ⟧Γ τ ⊢ ⟦ Φ ⟧Φ τ
wkTm↝ {τ = τ} x t = wkTm (⟦ x ⟧∋ τ) (! substV-eq x >₁ t)

\end{code}