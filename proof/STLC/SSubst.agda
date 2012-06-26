module STLC.SSubst where


open import STLC.Base

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
open ≡-Reasoning

infix 3 _=>_

data _=>_ : Con → Con → Set where
  sz : ∀ {Δ} → ε => Δ
  ss : ∀ {Γ Δ τ} → Γ => Δ → Tm Δ τ → Γ , τ => Δ

-- Changing the context in which a substitution is typed
!_>₂_ : forall {Γ Δ Δ'} → Δ ≡ Δ' → Γ => Δ → Γ => Δ'
! refl >₂ t = t

!sz : forall {Γ Δ} → (p : Γ ≡ Δ) → ! p >₂ sz ≡ sz
!sz refl = refl

!ss : forall {Γ Δ Δ' σ} → (p : Δ ≡ Δ') → (t : Tm Δ σ) → (s : Γ => Δ) → ! p >₂ ss s t ≡ ss (! p >₂ s) (! p >₁ t)
!ss refl _ _ = refl

-- Changing the domain of a substitution
!_>₃_ : forall {Γ Γ' Δ} → Γ ≡ Γ' → Γ => Δ → Γ' => Δ
! refl >₃ t = t
{-
!sz : forall {Γ Δ σ} → (p : Γ ≡ Δ) → (t : Tm Γ σ) → ! p >₂ sz t ≡ sz (! p >₁ t)
!sz refl _ = refl
-}

!ss' : forall {Γ Γ' Δ σ} → (p : Γ ≡ Γ') → (t : Tm Δ σ) → (s : Γ => Δ) → ! cong (\ x → x , σ) p >₃ ss s t ≡ ss (! p >₃ s) t
!ss' refl _ _ = refl


wkS : ∀ {Γ Δ τ} → (x : Var Δ τ) → Γ => Δ - x → Γ => Δ
wkS v sz        = sz
wkS v (ss y y') = ss (wkS v y) (wkTm v y')

!wkS : forall {Γ Γ' Δ σ} → (p : Γ ≡ Γ') → (a : Var Δ σ) → (s : Γ => Δ - a) → ! p >₃ wkS a s ≡ wkS a (! p >₃ s)
!wkS refl _ _ = refl

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

wkSI : {Γ Δ : Con} {τ : Ty} → (x : Var Γ τ) → (y : Var Δ τ) → Γ - x => Δ - y → Γ => Δ
wkSI x y v = extS x (var y) (wkS y v)

wkSI-extS : forall {Γ Δ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ)
      -> (a : Var Δ σ) → (u : Tm (Δ - a) τ)
      -> (s : ((Γ - x) - y) => Δ - a)
      -> extS (wkv x y) (wkTm a u) (wkSI (rem x y) a (! conExc x y >₃ s)) ≡ wkSI x a (extS y u s)
wkSI-extS x y a u s 
  = begin
  _ ≡⟨ cong (λ p → extS (wkv x y) (wkTm a u) (extS (rem x y) (var a) p)) (sym (!wkS (conExc x y) a s)) ⟩
  _ ≡⟨ extSExc x y (var a) (wkTm a u) (wkS a s) ⟩
  _ ≡⟨ cong (\p → extS x (var a) p) (wk-ext-comm y a u s) ⟩
  _ ∎

ιss : ∀ {Γ τ} → Γ => Γ → Γ , τ => Γ , τ
ιss = wkSI vz vz

ι : ∀ {Γ} → Γ => Γ
ι {ε}       = sz
ι {y , y'}  = ιss  (ι {y})

wkSI-ι : ∀ {Γ τ} → (v : Var Γ τ) → wkSI v v ι ≡ ι
wkSI-ι vz = refl
wkSI-ι (vs y) =
       begin
       _ ≡⟨ cong (λ p → ss (extS y (var (vs y)) p) (var vz)) (sym (wkSExc (vs y) vz ι)) ⟩
       _ ≡⟨ cong (λ p → ss p (var vz)) (wk-ext-comm y vz (var y) (wkS y ι)) ⟩
       _ ≡⟨ cong (λ p → ss (wkS vz p) (var vz)) (wkSI-ι y) ⟩
       _ ∎

lookup : ∀ {Γ Δ τ} → (v : Var Γ τ) → Γ => Δ → Tm Δ τ
lookup vz (ss y y')      = y'
lookup (vs y) (ss y' y0) = lookup y y'

wk-lookup : ∀ {Γ Δ τ σ} → (v : Var Γ τ) → (x : Var Δ σ) → (s : Γ => Δ - x) → lookup v (wkS x s) ≡ wkTm x (lookup v s)
wk-lookup vz x (ss y y') = refl
wk-lookup (vs y) x (ss y' y0) = wk-lookup y x y'

ι-lookup : ∀ {Γ τ} → (v : Var Γ τ) → lookup v ι ≡ var v
ι-lookup vz = refl
ι-lookup (vs y) = begin
         _ ≡⟨ wk-lookup y vz ι ⟩
         _ ≡⟨ cong weaken (ι-lookup y) ⟩
         _ ∎

ext-lookup : ∀ {Γ Δ τ} → (v : Var Γ τ) → (x : Tm Δ τ) → (s : Γ - v => Δ) → lookup v (extS v x s) ≡ x
ext-lookup vz x sz = refl
ext-lookup vz x (ss y y') = refl
ext-lookup (vs y) x (ss y' y0) = ext-lookup y x y'

ext-wkv-lookup : ∀ {Γ Δ τ σ} → (v : Var Γ τ) → (y : Var (Γ - v) σ) → (x : Tm Δ τ) 
               → (s : Γ - v => Δ) → lookup (wkv v y) (extS v x s) ≡ lookup y s
ext-wkv-lookup vz y x s = refl
ext-wkv-lookup (vs y) vz x (ss y0 y1) = refl
ext-wkv-lookup (vs y) (vs y') x (ss y0 y1) = ext-wkv-lookup y y' x y0

infix 8 _/_
_/_ : ∀ {Γ Δ τ} → Tm Γ τ → Γ => Δ → Tm Δ τ
_/_ (var y)     f = lookup y f
_/_ (Λ y)       f = Λ (y / wkSI vz vz f)
_/_ (app y y')  f = app (y / f) (y' / f)

wk/ : ∀ {Γ Δ τ σ} → (x : Var Δ σ) → (t : Tm Γ τ) → (s : Γ => Δ - x) 
               → t / wkS x s ≡ wkTm x (t / s)
wk/ x (var y) s = wk-lookup y x s
wk/ x (Λ y) s = begin
             _ ≡⟨ cong (λ v → Λ (y / extS vz (var vz) v)) (wkSExc (vs x) vz s) ⟩
             _ ≡⟨ cong (λ v → Λ (y / v)) (wk-ext-comm vz (vs x) (var vz) (wkS vz s))  ⟩
             _ ≡⟨ cong Λ (wk/ (vs x) y (wkSI vz vz s)) ⟩
             _ ∎
wk/ x (app y y') s = cong₂ app (wk/ x y s) (wk/ x y' s)

ι/ : ∀ {Γ τ} → (t : Tm Γ τ) → t / ι ≡ t
ι/ (var y)    = ι-lookup y
ι/ (Λ y)      = cong Λ (ι/ y)
ι/ (app y y') = cong₂ app (ι/ y) (ι/ y')

wk-ext/ : ∀ {Γ Δ τ σ} → (v : Var Γ σ) → (t : Tm (Γ - v) τ) → (x : Tm Δ σ) 
        → (s : Γ - v => Δ) → wkTm v t / extS v x s ≡ t / s
wk-ext/ v (var y) x s = ext-wkv-lookup v y x s
wk-ext/ v (Λ y) x s = begin
             _ ≡⟨ cong (λ p → Λ (wkTm (vs v) y / extS vz (var vz) p)) (sym (wk-ext-comm v vz x s)) ⟩
             _ ≡⟨ cong (λ p → Λ (wkTm (vs v) y / p)) (extSExc (vs v) vz (wkTm vz x) (var vz) (wkS vz s)) ⟩ 
             _ ≡⟨ cong Λ (wk-ext/ (vs v) y (wkTm vz x) (extS vz (var vz) (wkS vz s))) ⟩
             _ ∎ 
wk-ext/ v (app y y') x s = cong₂ app (wk-ext/ v y x s) (wk-ext/ v y' x s)

wkS-ext/ : ∀ {Γ Δ Δ' τ σ} → (v : Var Δ σ) → (t : Tm Γ τ) → (s : Γ => Δ - v) → (s' : Δ - v => Δ') 
           → (x : Tm Δ' σ) → (t / wkS v s) / extS v x s' ≡ (t / s) / s'
wkS-ext/ v (var y) s s' x = begin
                   _ ≡⟨ cong (\p → p / extS v x s') (wk-lookup y v s) ⟩
                   _ ≡⟨ wk-ext/ v (lookup y s) x s' ⟩
                   _ ∎
wkS-ext/ v (Λ y) s s' x = begin
                   _ ≡⟨ cong
                          (λ p → Λ ((y / ss p (var vz)) / ss (wkS vz (extS v x s')) (var vz)))
                          (sym (wkSExc vz v s)) ⟩
                   _ ≡⟨ cong
                          (λ p →
                             Λ ((y / ss (wkS (vs v) (wkS vz s)) (var vz)) / ss p (var vz)))
                          (sym (wk-ext-comm v vz x s')) ⟩
                   _ ≡⟨ cong Λ (wkS-ext/ (wkv vz v) y (ss (wkS vz s) (var vz)) (ss (wkS vz s') (var vz)) (wkTm vz x)) ⟩
                   _ ∎
wkS-ext/ v (app y y') s s' x = cong₂ app (wkS-ext/ v y s s' x) (wkS-ext/ v y' s s' x)
{-
dist-wkSI : ∀ {Γ Δ Δ' τ σ} → (v : Var Γ σ) → (w : Var Δ σ) → (u : Var Δ σ)
            → (t : Var Γ τ) → (s : Γ - v => Δ - w)
-}

dist-lookup : ∀ {Γ Δ τ σ} → (v : Var Γ σ) → (w : Var Δ σ) → (x : Tm (Δ - w) σ)
           → (y : Var Γ τ) → (s : Γ - v => Δ - w)
           → lookup y (extS v x s) ≡ lookup y (wkSI v w s) / extS w x ι
dist-lookup vz w x vz s = sym (ext-lookup w x ι)
dist-lookup (vs y) w x vz (ss y' y0) =
  begin
  _ ≡⟨ sym (ι/ y0) ⟩
  _ ≡⟨ sym (wk-ext/ w y0 x ι) ⟩
  _ ∎
dist-lookup vz w x (vs y) s 
  = begin
  _ ≡⟨ sym (ι/ (lookup y s)) ⟩
  _ ≡⟨ sym (wk-ext/ w (lookup y s) x ι) ⟩
  _ ≡⟨ cong (\p → p / extS w x ι) (sym (wk-lookup y w s)) ⟩
  _ ∎
dist-lookup (vs y) w x (vs y') (ss y0 y1) = dist-lookup y w x y' y0

dist-sub : ∀ {Γ Δ τ σ} → (v : Var Γ σ) → (t : Tm Γ τ) 
           → (w : Var Δ σ) → (x : Tm (Δ - w) σ)
           → (s : Γ - v => Δ - w)
           → t / extS v x s ≡ (t / wkSI v w s) / extS w x ι
dist-sub v (var y) w x s = dist-lookup v w x y s 
dist-sub v (Λ y) w x s 
  = begin
  _ ≡⟨ cong (λ p → Λ (y / ss p (var vz))) (sym (wk-ext-comm v vz x s)) ⟩
  _ ≡⟨ cong Λ (dist-sub (vs v) y (vs w) (wkTm vz x) (ss (wkS vz s) (var vz))) ⟩
  _ ≡⟨ cong₂
         (λ p1 p2 →
            Λ ((y / ss (extS v (var (vs w)) p1) (var vz)) / ss p2 (var vz)))
         (sym (wkSExc (vs w) vz s)) (wk-ext-comm w vz x ι) ⟩
  _ ≡⟨ cong (λ p → Λ ((y / ss p (var vz)) / wkSI vz vz (extS w x ι))) (wk-ext-comm v vz (var w) (wkS w s)) ⟩
  _ ∎
dist-sub v (app y y') w x s = cong₂ app (dist-sub v y w x s) (dist-sub v y' w x s)

wkSI/ : ∀ {Γ Δ τ σ} → (v : Var Γ σ) → (w : Var Δ σ) → (t : Tm (Γ - v) τ)
        → (s : Γ - v => Δ - w) → wkTm v t / wkSI v w s ≡ wkTm w (t / s)
wkSI/ v w (var y) s = begin
              _ ≡⟨ ext-wkv-lookup v y (var w) (wkS w s) ⟩
              _ ≡⟨ wk-lookup y w s ⟩
              _ ∎
wkSI/ v w (Λ y) s      =
             begin
             _ ≡⟨ cong (λ p → Λ (wkTm (vs v) y / ss p (var vz)))
                    (sym (wk-ext-comm v vz (var w) (wkS w s))) ⟩
             _ ≡⟨ cong
                    (λ p →
                       Λ (wkTm (vs v) y / extS (vs v) (var (vs w)) (ss p (var vz))))
                    (sym (wkSExc vz w s)) ⟩
             _ ≡⟨ cong Λ (wkSI/ (vs v) (vs w) y (ss (wkS vz s) (var vz))) ⟩
             _ ∎
wkSI/ v w (app y y') s = cong₂ app (wkSI/ v w y s) (wkSI/ v w y' s)

comm-/-lookup : ∀ {Γ Δ Δ' τ σ} → (v : Var Γ σ) → (y : Var Γ τ) 
           → (w : Var Δ σ) → (x : Tm (Δ - w) σ)
           → (s : Γ - v => Δ - w) → (s' : Δ - w => Δ')
           →  lookup y (extS v x s) / s' ≡ lookup y (wkSI v w s) / extS w (x / s') s'
comm-/-lookup vz vz w x s s' = sym (ext-lookup w (x / s') s')
comm-/-lookup vz (vs y) w x s s' 
  = begin
  _ ≡⟨ sym (wk-ext/ w (lookup y s) (x / s') s') ⟩
  _ ≡⟨ cong (\p → p / extS w (x / s') s') (sym (wk-lookup y w s)) ⟩
  _ ∎
comm-/-lookup (vs y) vz w x (ss y' y0) s' = sym (wk-ext/ w y0 (x / s') s')
comm-/-lookup (vs y) (vs y') w x (ss y0 y1) s' = comm-/-lookup y y' w x y0 s'

comm-/ : ∀ {Γ Δ Δ' τ σ} → (v : Var Γ σ) → (t : Tm Γ τ) 
       → (w : Var Δ σ) → (x : Tm (Δ - w) σ)
       → (s : Γ - v => Δ - w) → (s' : Δ - w => Δ')
       → (t / extS v x s) / s' ≡ (t / wkSI v w s) / extS w (x / s') s'
comm-/ v (var y) w x s s' = comm-/-lookup v y w x s s'
comm-/ v (Λ y) w x s s'
  = begin
  _ ≡⟨ cong (\p → Λ ((y / ss p (var vz)) / wkSI vz vz s')) (sym (wk-ext-comm v vz x s)) ⟩
  _ ≡⟨ cong Λ (comm-/ (vs v) y (vs w) (wkTm vz x) (ss (wkS vz s) (var vz)) (ss (wkS vz s') (var vz))) ⟩
  _ ≡⟨ cong₂
         (λ p1 p2 →
            Λ
            ((y / ss (extS v (var (vs w)) p1) (var vz)) /
             ss (extS w p2 (wkS vz s')) (var vz)))
         (sym (wkSExc (vs w) vz s)) (wkSI/ vz vz x s') ⟩
  _ ≡⟨ cong₂ (λ p1 p2 → Λ ((y / ss p1 (var vz)) / ss p2 (var vz))) (wk-ext-comm v vz (var w) (wkS w s)) (wk-ext-comm w vz (x / s') s') ⟩
  _ ∎
comm-/ v (app y y') w x s s' = cong₂ app (comm-/ v y w x s s') (comm-/ v y' w x s s')
{-
comm-/ : ∀ {Γ Δ Δ' τ σ} → (v : Var Γ σ) → (t : Tm Γ τ) 
       → (w : Var Δ σ) → (x : Tm (Δ - w) σ)
       → (s : Γ - v => Δ - w) → (s' : Δ - w => Δ')
-}
up-/sz : ∀ {Γ τ} → (t : Tm ε τ) → up {Γ} t ≡ t / sz
up-/sz (var ())
up-/sz {ε} (Λ y) = cong Λ (sym (ι/ y))
up-/sz {y , y'} (Λ y0) 
  = begin
  _ ≡⟨ cong (\p → wkTm vz p) (up-/sz {y} (Λ y0)) ⟩
  _ ≡⟨ cong Λ (sym (wkSI/ vz (vs vz) y0 (ss sz (var vz)))) ⟩
  _ ≡⟨ cong Λ (wk-ext/ vz y0 (var (vs vz)) (ss sz (var vz))) ⟩
  _ ∎
up-/sz (app y y') 
  = begin
  _ ≡⟨ sym (up-app y y') ⟩
  _ ≡⟨ cong₂ app (up-/sz y) (up-/sz y') ⟩
  _ ∎

wkS-ι : ∀ {Γ τ σ} → (v : Var Γ σ) → (t : Tm (Γ - v) τ) → t / wkS v ι ≡ wkTm v t
wkS-ι v t = trans (wk/ v t ι) (cong (λ p → wkTm v p) (ι/ t))

up/ε : ∀ {Γ τ} → (t : Tm ε τ) → (s : Γ => ε) → up t / s ≡ t
up/ε t sz = ι/ t
up/ε t (ss y y') = begin
               _ ≡⟨ wk-ext/ vz (up t) y' y ⟩
               _ ≡⟨ up/ε t y ⟩
               _ ∎

up/ : ∀ {Γ Δ τ} → (t : Tm ε τ) → (s : Γ => Δ) → up t / s ≡ up t
up/ {Γ} {ε} t s = up/ε t s
up/ {ε} {y , y'} t sz = begin
            _ ≡⟨ wk/ vz t sz ⟩
            _ ≡⟨ cong (\v → wkTm vz v) (up/ t sz) ⟩
            _ ∎
up/ {a , b} {y , y'} t (ss y0 y1) = begin
            _ ≡⟨ wk-ext/ vz (up t) y1 y0 ⟩
            _ ≡⟨ up/ t y0 ⟩
            _ ∎

sz/ : ∀ {Δ τ} → (t : Tm ε τ) → t / (sz {Δ}) ≡ up t
sz/ {ε} t      = ι/ t
sz/ {y , y'} t 
  = begin
  _ ≡⟨ wk/ vz t sz ⟩
  _ ≡⟨ cong (\p → wkTm vz p) (sz/ t) ⟩
  _ ∎

sub : ∀ {Γ τ} → (v : Var Γ τ) → (x : Tm (Γ - v) τ) → Γ => Γ - v
sub v x = extS v x ι

substVar-lookup : forall {σ Γ τ} → (v : Var Γ τ) → (x : Var Γ σ) → (t : Tm (Γ - x) σ)
           → substVar v x t ≡ lookup v (sub x t)
substVar-lookup v x t with eq x v
substVar-lookup v .v t | same = sym (ext-lookup v t ι)
substVar-lookup .(wkv x y) x t | diff .x y = trans (sym (ι-lookup y)) (sym (ext-wkv-lookup x y t ι))

subst/ : ∀ {Γ τ σ} → (v : Var Γ σ) → (t : Tm Γ τ) → (x : Tm (Γ - v) σ) → subst t v x ≡ t / sub v x
subst/ v (var y) x    = substVar-lookup y v x
subst/ v (Λ y) x      =
  begin
  _ ≡⟨ cong Λ (subst/ (vs v) y (wkTm vz x)) ⟩
  _ ≡⟨ cong (\p → Λ (y / ss p (var vz))) (wk-ext-comm v vz x ι)  ⟩
  _ ∎
subst/ v (app y y') x = cong₂ app (subst/ v y x) (subst/ v y' x)

wkTm-sub-comm : forall {Γ σ τ ρ} -> (y : Var Γ σ) -> (t : Tm (Γ - y) τ) -> (x : Var (Γ - y) ρ) -> (u : Tm ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (t / sub x u)) ≡ wkTm y t / sub (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTm-sub-comm y t x u
  = begin
  _ ≡⟨ cong (λ p → wkTm (rem y x) (! conExc y x >₁ p)) (sym (subst/ x t u)) ⟩
  _ ≡⟨ wkTmSubstExc y t x u ⟩
  _ ≡⟨ subst/ (wkv y x) (wkTm y t) (wkTm (rem y x) (! conExc y x >₁ u)) ⟩
  _ ∎