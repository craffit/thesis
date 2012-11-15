\begin{code}
module STLC.Term.Operations.Remove where

open import STLC.Variable
open import STLC.Term.Base
open import STLC.Term.Operations.Weaken
open import Util.PropositionalEquality

data Free {σ : Ty} : {Γ : Con} → {τ : Ty} → Γ ∋ σ → Γ ⊢ τ → Set where
  var : ∀ {Γ τ} → (v : Γ ∋ σ) → (x : Γ ∋ τ) → (y : Γ - v ∋ τ) 
      → x ≡ wkv v y → Free v (var x)
  Λ   : ∀ {Γ τ τ'} → (v : Γ ∋ σ) → (e : Γ , τ' ⊢ τ) → Free (vs v) e → Free v (Λ e)
  _·_   : ∀ {Γ τ τ'} → (v : Γ ∋ σ) → (f : Γ ⊢ τ' ⇒ τ) → (e : Γ ⊢ τ') 
        → Free v f → Free v e → Free v (f · e)

remove : ∀ {Γ σ τ} {v : Γ ∋ σ} → (e : Γ ⊢ τ) → Free v e → Γ - v ⊢ τ
remove {Γ} {σ} {τ} {v} .(var x) (var .v x y eq) = var y -- var y -- var x
remove {Γ} {σ} {(τ' ⇒ τ)} {v} .(Λ e) (Λ .v e y) = Λ (remove e y)
remove {Γ} {σ} {τ} {v} .(f · e) (_·_ .v f e y y') = remove f y · remove e y'

mkFree : ∀ {Γ σ τ} → (v : Γ ∋ σ) → (e : Γ - v ⊢ τ) → Free v (wkTm v e)
mkFree v (var y) = var v (wkv v y) y refl
mkFree v (Λ y) = Λ v (wkTm (vs v) y) (mkFree (vs v) y)
mkFree v (y · y') = (v · wkTm v y) (wkTm v y') (mkFree v y) (mkFree v y')

rem-wk : ∀ {Γ σ τ} {v : Γ ∋ σ} → (e : Γ - v ⊢ τ) → (f : Free v (wkTm v e)) 
       → remove (wkTm v e) f ≡ e
rem-wk {Γ} {σ} {τ} {v} (var y) (var .v .(wkv v y) y' y0) = {!!}
rem-wk (Λ y) f = {!!}
rem-wk (y · y') f = {!!}
{-
mkFree : ∀ {Γ σ τ} → (v : Γ ∋ σ) → (e : Γ - v ⊢ τ) → Free v (wkTm v e)
mkFree v e = Release e
-}

\end{code}