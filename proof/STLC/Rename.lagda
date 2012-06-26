\begin{code}
module STLC.Rename where

open import STLC.Base
open import STLC.Context
open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
open ≡-Reasoning

infix 3 _=>>_

data _=>>_ : Con → Con → Set where
  rz : ∀ {Δ} → ε =>> Δ
  rs : ∀ {Γ Δ τ} → Γ =>> Δ → Var Δ τ → Γ , τ =>> Δ

-- Changing the context in which a renaming is typed
!_>r_ : forall {Γ Δ Δ'} → Δ ≡ Δ' → Γ =>> Δ → Γ =>> Δ'
! refl >r t = t

!rz : forall {Γ Δ} → (p : Γ ≡ Δ) → ! p >r rz ≡ rz
!rz refl = refl

!rs : forall {Γ Δ Δ' σ} → (p : Δ ≡ Δ') → (t : Var Δ σ) → (s : Γ =>> Δ) → ! p >r rs s t ≡ rs (! p >r s) (! p >₀ t)
!rs refl _ _ = refl

-- Changing the domain of a renaming
!_>r'_ : forall {Γ Γ' Δ} → Γ ≡ Γ' → Γ =>> Δ → Γ' =>> Δ
! refl >r' t = t

!rs' : forall {Γ Γ' Δ σ} → (p : Γ ≡ Γ') → (t : Var Δ σ) → (s : Γ =>> Δ) → ! cong (\ x → x , σ) p >r' rs s t ≡ rs (! p >r' s) t
!rs' refl _ _ = refl

wkR : ∀ {Γ Δ τ} → (x : Var Δ τ) → Γ =>> Δ - x → Γ =>> Δ
wkR v rz        = rz
wkR v (rs y y') = rs (wkR v y) (wkv v y')

wkRExc : forall {Γ Δ σ τ} -> (x : Var Δ σ) -> (y : Var (Δ - x) τ) 
      -> (s : Γ =>> ((Δ - x) - y)) 
      -> wkR (wkv x y) (wkR (rem x y) (! conExc x y >r s)) ≡ wkR x (wkR y s)
wkRExc x y rz = cong (λ v → wkR (wkv x y) (wkR (rem x y) v)) (!rz (conExc x y))
wkRExc x y (rs y' y0) = begin
       _ ≡⟨ cong (λ v → wkR (wkv x y) (wkR (rem x y) v)) (!rs (conExc x y) y0 y') ⟩
       _ ≡⟨ cong₂ rs (wkRExc x y y') (wkvExc x y y0) ⟩
       _ ∎

extR : ∀ {Γ Δ τ} → (x : Var Γ τ) → (t : Var Δ τ) → Γ - x =>> Δ → Γ =>> Δ
extR vz t s              = rs s t
extR (vs y) t (rs y' y0) = rs (extR y t y') y0

extRExc : forall {Γ Δ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ)
      -> (t : Var Δ σ) → (u : Var Δ τ)
      -> (s : ((Γ - x) - y) =>> Δ)
      -> extR (wkv x y) u (extR (rem x y) t (! conExc x y >r' s)) ≡ extR x t (extR y u s)
extRExc vz y t u s = refl
extRExc (vs y) vz t u s = refl
extRExc (vs y) (vs y') t u (rs y0 y1) = begin
        _ ≡⟨ cong
               (λ v → extR (vs (wkv y y')) u (extR (vs (rem y y')) t v))
               (!rs' (conExc y y') y1 y0) ⟩
        _ ≡⟨ cong (λ v → rs v y1) (extRExc y y' t u y0) ⟩
        _ ∎
{-
wk-ext-comm : ∀ {Γ Δ τ σ} (x : Var Γ τ) → (y : Var Δ σ) → (t : Tm (Δ - y) τ)
                → (s : Γ - x => Δ - y) → extS x (wkTm y t) (wkS y s) ≡ wkS y (extS x t s)
wk-ext-comm vz y t s = refl
wk-ext-comm (vs y) y' t (ss y0 y1) = cong (λ z → ss z (wkTm y' y1)) (wk-ext-comm y y' t y0)
-}

expR : ∀ {Γ Δ τ} → (x : Var Γ τ) → (y : Var Δ τ) → Γ - x =>> Δ - y → Γ =>> Δ
expR x y s = extR x y (wkR y s)

expRι : ∀ {Γ Δ τ} → Γ =>> Δ → Γ , τ =>> Δ , τ
expRι = expR vz vz

lookupr : ∀ {Γ Δ τ} → Γ =>> Δ → Var Γ τ → Var Δ τ
lookupr rz ()
lookupr (rs y y') vz      = y'
lookupr (rs y y') (vs y0) = lookupr y y0

ιr : (Γ : Con) → Γ =>> Γ
ιr ε        = rz
ιr (y , y') = expR vz vz (ιr y)


infix 8 _/r_
_/r_ : ∀ {Γ Δ τ} → Tm Γ τ → Γ =>> Δ → Tm Δ τ
_/r_ (var y)     f = var (lookupr f y)
_/r_ (Λ y)       f = Λ (y /r  expRι f)
_/r_ (app y y')  f = app (y /r f) (y' /r f)

wkTmR : ∀ {Γ τ σ} → (x : Var Γ σ) → Tm (Γ - x) τ → Tm Γ τ
wkTmR x t = t /r wkR x (ιr _)

upR : ∀ {Γ Δ} → Γ =>> Δ ▸▸ Γ
upR {Γ} {ε}      = ≡subst (\v → Γ =>> v) (sym (ε▸▸ {Γ})) (ιr Γ)
upR {Γ} {y , y'} = wkR (exVar {y , y'} {Γ} (vz {y} {y'})) (≡subst (λ v → Γ =>> v) (ex- {y , y'} {Γ} vz) (upR {Γ} {y}))

up' : ∀ {Γ Δ τ} → Tm Γ τ → Tm (Δ ▸▸ Γ) τ
up' {Γ} {ε} t = {!!}
up' {Γ} {y , y'} t = {!!} 

upΛ : ∀ {Γ Δ τ σ} → (t : Tm (Γ , σ) τ) → up' {Γ} {Δ} (Λ t) ≡ Λ (up' {Γ , σ} {Δ} t)
upΛ (var y) = {!!}
upΛ (Λ y) = {!!}
upΛ (app y y') = {!!}

{-
!sz : forall {Γ Δ σ} → (p : Γ ≡ Δ) → (t : Tm Γ σ) → ! p >₂ sz t ≡ sz (! p >₁ t)
!sz refl _ = refl
-}
{-
!ss' : forall {Γ Γ' Δ σ} → (p : Γ ≡ Γ') → (t : Tm Δ σ) → (s : Γ => Δ) → ! cong (\ x → x , σ) p >₃ ss s t ≡ ss (! p >₃ s) t
!ss' refl _ _ = refl

wkS : ∀ {Γ Δ τ} → (x : Var Δ τ) → Γ => Δ - x → Γ => Δ
wkS v sz        = sz
wkS v (ss y y') = ss (wkS v y) (wkTm v y')


wkSExc : forall {Γ Δ σ τ} -> (x : Var Δ σ) -> (y : Var (Δ - x) τ) 
      -> (s : Γ => ((Δ - x) - y)) 
      -> wkS (wkv x y) (wkS (rem x y) (! conExc x y >₂ s)) ≡ wkS x (wkS y s)
wkSExc x y sz = cong (λ v → wkS (wkv x y) (wkS (rem x y) v)) (!sz (conExc x y))
wkSExc x y (ss y' y0) = begin
       _ ≡⟨ cong (λ v → wkS (wkv x y) (wkS (rem x y) v)) (!ss (conExc x y) y0 y') ⟩
       _ ≡⟨ cong₂ ss (wkSExc x y y') (wkTmExc x y y0) ⟩
       _ ∎

extS : ∀ {Γ Δ τ} → (x : Var Γ τ) → (t : Tm Δ τ) → Γ - x => Δ → Γ => Δ
extS vz t s              = ss s t
extS (vs y) t (ss y' y0) = ss (extS y t y') y0

extSExc : forall {Γ Δ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ)
      -> (t : Tm Δ σ) → (u : Tm Δ τ)
      -> (s : ((Γ - x) - y) => Δ)
      -> extS (wkv x y) u (extS (rem x y) t (! conExc x y >₃ s)) ≡ extS x t (extS y u s)
extSExc vz y t u s = refl
extSExc (vs y) vz t u s = refl
extSExc (vs y) (vs y') t u (ss y0 y1) = begin
        _ ≡⟨ cong
               (λ v → extS (vs (wkv y y')) u (extS (vs (rem y y')) t v))
               (!ss' (conExc y y') y1 y0) ⟩
        _ ≡⟨ cong (λ v → ss v y1) (extSExc y y' t u y0) ⟩
        _ ∎
wk-ext-comm : ∀ {Γ Δ τ σ} (x : Var Γ τ) → (y : Var Δ σ) → (t : Tm (Δ - y) τ)
                → (s : Γ - x => Δ - y) → extS x (wkTm y t) (wkS y s) ≡ wkS y (extS x t s)
wk-ext-comm vz y t s = refl
wk-ext-comm (vs y) y' t (ss y0 y1) = cong (λ z → ss z (wkTm y' y1)) (wk-ext-comm y y' t y0)
-}
\end{code}
