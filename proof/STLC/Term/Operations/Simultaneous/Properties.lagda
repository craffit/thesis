%if False

\begin{code}
module STLC.Term.Operations.Simultaneous.Properties where

open import STLC.Variable
open import STLC.Term.Base
open import STLC.Term.Operations.Weaken
open import STLC.Term.Congruence
open import STLC.Term.Operations.Simultaneous.Base
open import STLC.Term.Operations.Simultaneous.Congruence

open import Util.PropositionalEquality
open ≡-Reasoning
 
wkSExc : ∀ {Γ Δ σ τ} → (x : Δ ∋ σ) → (y : Δ - x ∋ τ) → (s : Γ => Δ - x - y) 
      → wkS (wkv x y) (wkS (rem x y) (! ≡Γrefl , Γ-- x y >=> s)) ≡ wkS x (wkS y s)
wkSExc x y sz = refl
wkSExc x y (ss y' y0) = ≡ss (wkSExc x y y') (wkTmExc x y y0)

wkSExcvz : ∀ {Γ Δ σ τ} -> (x : Δ ∋ σ) -> (s : Γ => Δ - x) 
        → wkS {τ} vz (wkS x s) ≡ wkS (vs x) (wkS vz s)
wkSExcvz x s =
  begin
  _ ≡⟨ ≡wkS vz (≡wkS x (sym (!,=>-id ≡Γrefl ≡Γrefl s))) ⟩
  _ ≡⟨ wkSExc (vs x) vz s ⟩
  _ ∎

extSExc : ∀ {Γ Δ σ τ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → (t : Δ ⊢ σ) → (u : Δ ⊢ τ)
      -> (s : Γ - x - y => Δ)
      -> extS (wkv x y) u (extS (rem x y) t (! Γ-- x y , ≡Γrefl >=> s)) 
       ≡ extS x t (extS y u s)
extSExc vz y t u s = ≡ss (≡extS y refl (!,=>-id ≡Γrefl ≡Γrefl s)) refl
extSExc (vs y) vz t u s = ≡ss (≡extS y refl (!,=>-id ≡Γrefl ≡Γrefl s)) refl
extSExc (vs y) (vs y') t u (ss y0 y1) = ≡ss (extSExc y y' t u y0) (!,⊢-id ≡Γrefl ≡τrefl y1)

wk-ext-comm : ∀ {Γ Δ τ σ} (x : Γ ∋ τ) → (y : Δ ∋ σ) → (t : Δ - y ⊢ τ)
            → (s : Γ - x => Δ - y) → extS x (wkTm y t) (wkS y s) ≡ wkS y (extS x t s)
wk-ext-comm vz y t s = refl
wk-ext-comm (vs y) y' t (ss y0 y1) = ≡ss (wk-ext-comm y y' t y0) refl

-- Weakening and extending of substitutions

wk-lookup : ∀ {Γ Δ τ σ} → (v : Γ ∋ τ) → (x : Δ ∋ σ) → (s : Γ => Δ - x) → lookup v (wkS x s) ≡ wkTm x (lookup v s)
wk-lookup vz x (ss y y') = refl
wk-lookup (vs y) x (ss y' y0) = wk-lookup y x y'

wk/ : ∀ {Γ Δ τ σ} → (x : Δ ∋ σ) → (t : Γ ⊢ τ) → (s : Γ => Δ - x) 
               → t / wkS x s ≡ wkTm x (t / s)
wk/ x (var y) s = wk-lookup y x s
wk/ x (Λ y) s = begin
             _ ≡⟨ ≡Λ ( ■' y ≡/ ≡extS vz refl (wkSExcvz x s)) ⟩
             _ ≡⟨ ≡Λ ( ■' y ≡/ wk-ext-comm vz (vs x) (var vz) (wkS vz s))  ⟩
             _ ≡⟨ ≡Λ (wk/ (vs x) y (wkExtS vz vz s)) ⟩
             _ ∎
wk/ x (y · y') s = wk/ x y s ≡· wk/ x y' s

ext-lookup : ∀ {Γ Δ τ} → (v : Γ ∋ τ) → (x : Δ ⊢ τ) → (s : Γ - v => Δ) → lookup v (extS v x s) ≡ x
ext-lookup vz x sz = refl
ext-lookup vz x (ss y y') = refl
ext-lookup (vs y) x (ss y' y0) = ext-lookup y x y'

ext-wkv-lookup : ∀ {Γ Δ τ σ} → (v : Γ ∋ τ) → (y : Γ - v ∋ σ) → (x : Δ ⊢ τ) 
               → (s : Γ - v => Δ) → lookup (wkv v y) (extS v x s) ≡ lookup y s
ext-wkv-lookup vz y x s = refl
ext-wkv-lookup (vs y) vz x (ss y0 y1) = refl
ext-wkv-lookup (vs y) (vs y') x (ss y0 y1) = ext-wkv-lookup y y' x y0

wk-ext/ : ∀ {Γ Δ τ σ} → (v : Γ ∋ σ) → (t : Γ - v ⊢ τ) → (x : Δ ⊢ σ) 
        → (s : Γ - v => Δ) → wkTm v t / extS v x s ≡ t / s
wk-ext/ v (var y) x s = ext-wkv-lookup v y x s
wk-ext/ v (Λ y) x s = 
  begin
  _ ≡⟨ ≡Λ (■' (wkTm (vs v) y) ≡/ ≡extS vz refl (sym (wk-ext-comm v vz x s))) ⟩
  _ ≡⟨ ≡Λ (wk-ext/ (vs v) y (wkTm vz x) (extS vz (var vz) (wkS vz s))) ⟩
  _ ∎ 
wk-ext/ v (y · y') x s = wk-ext/ v y x s ≡· wk-ext/ v y' x s

wk-wkExtS/ : ∀ {Γ Δ τ σ} → (v : Γ ∋ σ) → (w : Δ ∋ σ) → (t : Γ - v ⊢ τ)
        → (s : Γ - v => Δ - w) → wkTm v t / wkExtS v w s ≡ wkTm w (t / s)
wk-wkExtS/ v w t s =
  begin
  _ ≡⟨ wk-ext/ v t (var w) (wkS w s) ⟩
  _ ≡⟨ wk/ w t s ⟩
  _ ∎

-- Weakening and extending of of /=>

wkS-wkS/=> : ∀ {Γ Δ Δ' τ} → (v : Δ' ∋ τ) → (s : Γ => Δ) → (s' : Δ => Δ' - v) 
          → s /=> wkS v s' ≡ wkS v (s /=> s')
wkS-wkS/=> v sz s' = refl
wkS-wkS/=> v (ss y y') s' = ≡ss (wkS-wkS/=> v y s') (wk/ v y' s') 

wkS-extS/=> : ∀ {Γ Δ Δ' τ} → (v : Δ ∋ τ) → (x : Δ' ⊢ τ) → (s : Γ => Δ - v) 
            → (s' : Δ - v => Δ') → wkS v s /=> extS v x s' ≡ s /=> s'
wkS-extS/=> v x sz s' = refl
wkS-extS/=> v x (ss y y') s' = ≡ss (wkS-extS/=> v x y s') (wk-ext/ v y' x s')

wkS-wkExtS/=> : ∀ {Γ Δ Δ' τ} → (v : Δ ∋ τ) → (v' : Δ' ∋ τ)
          → (s : Γ => Δ - v) → (s' : Δ - v => Δ' - v') 
          → wkS v s /=> wkExtS v v' s' ≡ wkS v' (s /=> s')
wkS-wkExtS/=> v v' s s' =
  begin
  _ ≡⟨ wkS-extS/=> v (var v') s (wkS v' s') ⟩
  _ ≡⟨ wkS-wkS/=> v' s s' ⟩
  _ ∎

-- Transforming between / and /=>

lookup/ : ∀ {Γ Δ Δ' τ} → (y : Γ ∋ τ) → (s : Γ => Δ) → (s' : Δ => Δ')
        → lookup y s / s' ≡ lookup y (s /=> s')
lookup/ vz (ss y y') s' = refl
lookup/ (vs y) (ss y' y0) s' = lookup/ y y' s'

merge-/ : ∀ {Γ Δ Δ' τ} → (t : Γ ⊢ τ) → (s : Γ => Δ) → (s' : Δ => Δ')
           → t / s / s' ≡ t / s /=> s'
merge-/ (var y) s s' = lookup/ y s s'
merge-/ (Λ y) s s' =
     begin 
     _ ≡⟨ ≡Λ (merge-/ y (ss (wkS vz s) (var vz)) (ss (wkS vz s') (var vz))) ⟩
     _ ≡⟨ ≡Λ (■' y ≡/ ≡ss (wkS-wkExtS/=> vz vz s s') ■) ⟩
     _ ∎
merge-/ (y · y') s s' = merge-/ y s s' ≡· merge-/ y' s s'

split-/ : ∀ {Γ Δ Δ' τ} → (t : Γ ⊢ τ) → (s : Γ => Δ) → (s' : Δ => Δ')
           → t / s /=> s' ≡ t / s / s' 
split-/ t s s' = sym (merge-/ t s s')

-- Proofs involving ι

ι-lookup : ∀ {Γ τ} → (v : Γ ∋ τ) → lookup v ι ≡ var v
ι-lookup vz = refl
ι-lookup (vs y) = begin
         _ ≡⟨ wk-lookup y vz ι ⟩
         _ ≡⟨ cong weaken (ι-lookup y) ⟩
         _ ∎

/ι : ∀ {Γ τ} → (t : Γ ⊢ τ) → t / ι ≡ t
/ι (var y)   = ι-lookup y
/ι (Λ y)     = ≡Λ (/ι y)
/ι (y · y')  = /ι y ≡· /ι y'

wkExtS-ι : ∀ {Γ τ} → (v : Γ ∋ τ) → wkExtS v v ι ≡ ι
wkExtS-ι vz = refl
wkExtS-ι (vs y) =
       begin
       _ ≡⟨ ≡ss (≡extS y refl (sym (wkSExcvz y ι))) refl ⟩
       _ ≡⟨ ≡ss (wk-ext-comm y vz (var y) (wkS y ι)) refl ⟩
       _ ≡⟨ ≡ss (≡wkS vz (wkExtS-ι y)) refl ⟩
       _ ∎

/=>ι : ∀ {Γ Δ} → (s : Γ => Δ) → s /=> ι ≡ s
/=>ι sz = refl
/=>ι (ss y y') = cong₂ ss (/=>ι y) (/ι y')

ι/=> : ∀ {Γ Δ} → (s : Γ => Δ) → ι /=> s ≡ s
ι/=> sz = refl
ι/=> (ss y y') = cong (λ v → ss v y') (trans (wkS-extS/=> vz y' ι y) (ι/=> y))

wkTm/sub : ∀ {Γ σ τ} -> (y : Γ ∋ σ) → (t : Γ - y ⊢ τ) → (u : Γ - y ⊢ σ) 
         → wkTm y t / sub y u ≡ t
wkTm/sub y t u =
  begin
  _ ≡⟨ wk-ext/ y t u ι ⟩
  _ ≡⟨ /ι t ⟩
  _ ∎

{-
wkS-ι : ∀ {Γ τ σ} → (v : _∋_ Γ σ) → (t : _⊢_ (Γ - v) τ) → t / wkS v ι ≡ wkTm v t
wkS-ι v t = trans (wk/ v t ι) (cong (λ p → wkTm v p) (/ι t))

substVar-lookup : ∀ {σ Γ τ} → (v : _∋_ Γ τ) → (x : _∋_ Γ σ) → (t : _⊢_ (Γ - x) σ)
           → substVar v x t ≡ lookup v (sub x t)
substVar-lookup v x t with eq x v
substVar-lookup v .v t | same = sym (ext-lookup v t ι)
substVar-lookup .(wkv x y) x t | diff .x y = trans (sym (ι-lookup y)) (sym (ext-wkv-lookup x y t ι))

subst/ : ∀ {Γ τ σ} → (v : _∋_ Γ σ) → (t : _⊢_ Γ τ) → (x : _⊢_ (Γ - v) σ) → subst t v x ≡ t / sub v x
subst/ v (var y) x    = substVar-lookup y v x
subst/ v (Λ y) x      =
  begin
  _ ≡⟨ cong Λ (subst/ (vs v) y (wkTm vz x)) ⟩
  _ ≡⟨ cong (\p → Λ (y / ss p (var vz))) (wk-ext-comm v vz x ι)  ⟩
  _ ∎
subst/ v (y · y') x = cong₂ _·_ (subst/ v y x) (subst/ v y' x)

wkTm-sub-comm : ∀ {Γ σ τ ρ} -> (y : _∋_ Γ σ) -> (t : _⊢_ (Γ - y) τ) -> (x : _∋_ (Γ - y) ρ) -> (u : _⊢_ ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (t / sub x u)) ≡ wkTm y t / sub (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTm-sub-comm y t x u
  = begin
  _ ≡⟨ cong (λ p → wkTm (rem y x) (! conExc y x >₁ p)) (sym (subst/ x t u)) ⟩
  _ ≡⟨ wkTmSubstExc y t x u ⟩
  _ ≡⟨ subst/ (wkv y x) (wkTm y t) (wkTm (rem y x) (! conExc y x >₁ u)) ⟩
  _ ∎
-}
\end{code}
%endif
