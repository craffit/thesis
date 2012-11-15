%if False
\begin{code}
module STLC.Term.Convertibility where

open import Relation.Binary hiding (_⇒_)
open import STLC.Variable
open import STLC.Term.Base
open import STLC.Term.Operations.Weaken
open import STLC.Term.Operations.Simultaneous
open import Util.PropositionalEquality
import Relation.Binary.EqReasoning

infixl 7 _⟷_
infix 1 _βη-≡_
infix 1 _βη-=>_
infixl 3 _%·_
infixl 8 _%/-_
infixl 8 _-%/_
infixl 8 _%/_

data _βη-≡_ {Γ : Con} : {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → Set where
  □     : ∀ {σ} → {t : Γ ⊢ σ} → t βη-≡ t
  bsym  : ∀ {σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  _⟷_   : ∀ {σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  %Λ_   : ∀ {σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  _%·_  : ∀ {σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} 
        → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ →  t₁ · u₁ βη-≡ t₂ · u₂
  beta  : ∀ {σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u βη-≡ t / sub vz u
  eta   : ∀ {σ τ} → {t : Γ ⊢ σ ⇒ τ} → Λ (wkTm vz t · var vz) βη-≡ t
 
data _βη-=>_ {Δ : Con} : {Γ : Con} → Γ => Δ → Γ => Δ → Set where
  sz : sz βη-=> sz
  ss : ∀ {Γ τ} {s1 s2 : Γ => Δ} {t1 t2 : Δ ⊢ τ} 
     → s1 βη-=> s2 → t1 βη-≡ t2 → ss s1 t1 βη-=> ss s2 t2

=>refl : ∀ {Γ Δ} {s : Γ => Δ} → s βη-=> s
=>refl {.ε} {Δ} {sz} = sz
=>refl {Γ , τ} {Δ} {ss y y'} = ss (=>refl {Γ} {Δ} {y}) □

=>sym : ∀ {Γ Δ} {s s' : Γ => Δ} → s βη-=> s' → s' βη-=> s
=>sym sz = sz
=>sym (ss y y') = ss (=>sym y) (bsym y')

=>trans : ∀ {Γ Δ} {s s' s'' : Γ => Δ} → s βη-=> s' → s' βη-=> s'' → s βη-=> s''
=>trans sz p2 = p2
=>trans (ss y y') (ss y0 y1) = ss (=>trans y y0) (y' ⟷ y1)


βηsetoid : {Γ : Con} {σ : Ty} → Setoid _ _
βηsetoid {Γ} {σ} = 
  record { Carrier = Γ ⊢ σ 
         ; _≈_ = _βη-≡_
         ; isEquivalence = 
              record { refl  = □
                     ; sym   = bsym
                     ; trans = _⟷_
                     }                              
         }

βη=>setoid : {Γ Δ : Con} → Setoid _ _
βη=>setoid {Γ} {Δ} = 
  record { Carrier = Γ => Δ 
         ; _≈_ = _βη-=>_
         ; isEquivalence = 
              record { refl  = =>refl
                     ; sym   = =>sym
                     ; trans = =>trans
                     }                              
         }

-- Congruences of βη-≡

□' : ∀ {Γ τ} (t : Γ ⊢ τ) → t βη-≡ t
□' _ = □

%≡_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
%≡_ refl = □

=>≡ : ∀ {Γ Δ} → {t1 t2 : Γ => Δ} → t1 ≡ t2 → t1 βη-=> t2
=>≡ refl = =>refl

-- beta' : ∀ {Γ σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u βη-≡ subst t vz u
-- beta' {t = t} {u = u} = beta ⟷ bsym (equiv (subst/ vz t u))
{-
congSubstVar : ∀ {σ Γ τ} → (v : Γ ∋ τ) → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl
-}

%wkTm : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
%wkTm _ □ = □
%wkTm x (bsym p) = bsym (%wkTm x p)
%wkTm x (p₁ ⟷ p₂) = %wkTm x p₁ ⟷ %wkTm x p₂
%wkTm x (%Λ p) = %Λ %wkTm (vs x) p
%wkTm x (p₁ %· p₂) = %wkTm x p₁ %· %wkTm x p₂
%wkTm x {Λ t · u} beta =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ %≡ (■' (wkTm (vs x) t) ≡/ ≡ss (sym (wkExtS-ι x)) refl) ⟩
       _ ⟷⟨ %≡ wk-ext/ (vs x) t (var x) (ss (wkS x ι) (wkTm x u)) ⟩
       _  ⟷⟨ %≡ wk/ x t (ss ι u) ⟩
       _ ∎
%wkTm x {._} {t} eta = %Λ (%≡ sym (wkTmExcvz x t) %· □) ⟷ eta

%lookup : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (y : Γ ∋ τ) → lookup y s βη-≡ lookup y s'
%lookup {ε} sz ()
%lookup {y , .τ} {Δ} {τ} (ss y0 y1) vz = y1
%lookup {y , y'} (ss y0 y1) (vs y2) = %lookup y0 y2

%extS : ∀ {Γ Δ τ} {t t' : Δ ⊢ τ} → (v : Γ ∋ τ) → {s s' : Γ - v => Δ} → s βη-=> s' → t βη-≡ t' → extS v t s βη-=> extS v t' s'
%extS vz s0 t0 = ss s0 t0
%extS (vs y) (ss y' y0) t0 = ss (%extS y y' t0) y0

%wkS : ∀ {Γ Δ τ}  → (v : Δ ∋ τ) → {s s' : Γ => Δ - v} → s βη-=> s' 
     → wkS v s βη-=> wkS v s'
%wkS v sz = sz
%wkS v (ss y y') = ss (%wkS v y) (%wkTm v y')

_%/-_ : ∀ {Γ Δ τ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → (s : Γ => Δ) → t / s βη-≡ t' / s
_%/-_ □ s = □
_%/-_ (bsym y) s = bsym (y %/- s)
_%/-_ (y ⟷ y') s = y %/- s ⟷ y' %/- s
_%/-_ (%Λ y) s = %Λ (y %/- (ss (wkS vz s) (var vz)))
_%/-_ (y %· y') s = y %/- s %· y' %/- s
_%/-_ (beta {_} {_} {t} {u}) s =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ %≡ merge-/ t _ _ ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (wkS-extS/=> vz (u / s) s ι) refl) ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (/=>ι s) refl) ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (sym (ι/=> s)) refl) ⟩
       _ ⟷⟨ %≡ split-/ t _ _ ⟩
      _ ∎
_%/-_ (eta {_} {_} {t}) s = %Λ (%≡ wk-wkExtS/ vz vz t s %· □) ⟷ eta

_-%/_ : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → (t : Γ ⊢ τ) → s βη-=> s' → t / s βη-≡ t / s'
_-%/_ (var y) s  = %lookup s y
_-%/_ (Λ y) s    = %Λ (y -%/ %extS vz (%wkS vz s) □)
_-%/_ (y · y') s = y -%/ s %· y' -%/ s

_%/_ : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → s βη-=> s'
    → t / s βη-≡ t' / s'
_%/_ {t' = t'} □ s = t' -%/ s
_%/_ (bsym y) s  = bsym (y %/ =>sym s)
_%/_ (y ⟷ y') s = y %/ s ⟷ y' %/ =>refl
_%/_ (%Λ y) s   = %Λ (y %/ (ss (%wkS vz s) □))
_%/_ (y %· y') s = y %/ s %· y' %/ s
_%/_ {s = s} {s' = s'} (beta {t = t} {u = u}) sb =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ beta ⟩
     _ ⟷⟨ %≡ merge-/ t _ _ ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (wkS-extS/=> vz (u / s) s ι) refl) ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (/=>ι s) refl) ⟩
     _ ⟷⟨ t -%/ ss sb (u -%/ sb) ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (sym (ι/=> s')) refl) ⟩
     _ ⟷⟨ %≡ split-/ t _ _ ⟩
     _ ∎
_%/_ (eta {t = t}) s =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %Λ (%≡ wk-wkExtS/ vz vz t _ %· □) ⟩
     _ ⟷⟨ %Λ (%wkTm vz (t -%/ s) %· □) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

ext : ∀ {Γ σ τ} → (e e' : Γ ⊢ σ ⇒ τ) → wkTm vz e · var vz βη-≡ wkTm vz e' · var vz 
    → e βη-≡ e'
ext e e' eq =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ eq ⟩
     _ ⟷⟨ eta ⟩
     _ ∎  
{-
congSubst : ∀ {σ Γ τ} → (t : Γ ⊢ τ) → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ σ} → u₁ βη-≡ u₂ → subst t x u₁ βη-≡ subst t x u₂
congSubst (var v) x p = congSubstVar v x p
congSubst (Λ t) x p = congΛ (congSubst t (vs x) (%wkTm vz p))
congSubst (t₁ · t₂) x p = congApp (congSubst t₁ x p) (congSubst t₂ x p)
-}


{-
congSubst' : ∀ {σ Γ τ} → {t1 t2 : Γ ⊢ τ} → t1 βη-≡ t2 → (x : Γ ∋ σ) 
           → (u : Γ - x ⊢ σ) → subst t1 x u βη-≡ subst t2 x u
congSubst' {t1 = t1} {t2 = t2} eq x u =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ equiv (subst/ x t1 u) ⟩
     _ ⟷⟨ cong/ eq (extS x u ι) ⟩
     _ ⟷⟨ bsym (equiv (subst/ x t2 u)) ⟩
     _ ∎
cong-lookup-s : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (y : Γ ∋ τ) → lookup y s βη-≡ lookup y s'
cong-lookup-s {ε} sz ()
cong-lookup-s {y , .τ} {Δ} {τ} (ss y0 y1) vz = y1
cong-lookup-s {y , y'} (s%wkTms y0 y1) (vs y2) = cong-lookup-s y0 y2

cong-extS : ∀ {Γ Δ τ} {t t' : Δ ⊢ τ} → (v : Γ ∋ τ) → {s s' : Γ - v => Δ} → s βη-=> s' → t βη-≡ t' → extS v t s βη-=> extS v t' s'
cong-extS vz s0 t0 = ss s0 t0
cong-extS (vs y) (ss y' y0) t0 = ss (cong-extS y y' t0) y0

cong-wkS : ∀ {Γ Δ τ}  → (v : Δ ∋ τ) → {s s' : Γ => Δ - v} → s βη-=> s' → wkS v s βη-=> wkS v s'
cong-wkS v sz = sz
cong-wkS v (ss y y') = ss (cong-wkS v y) (%wkTm v y')

cong/s : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (t : Γ ⊢ τ) → t / s βη-≡ t / s'
cong/s s0 (var y) = cong-lookup-s s0 y
cong/s s0 (Λ y) = congΛ (cong/s (cong-extS vz (cong-wkS vz s0) brefl) y)
cong/s s0 (y · y') = congApp (cong/s s0 y) (cong/s s0 y')

-- substEqV : ∀ {Γ σ τ} → (v : Γ ∋ σ) → (e : Γ ⊢ τ) → subst e v (var v)
-- substEqV v e = ? 
·vz : ∀ {Γ σ τ} → (e e' : Γ ⊢ σ ⇒ τ) → wkTm vz e · var vz βη-≡ wkTm vz e' · var vz 
    → e βη-≡ e'
·vz e e' eq =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ congΛ eq ⟩
     _ ⟷⟨ eta ⟩
     _ ∎
/eq : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → {t t' : Γ ⊢ τ} → s βη-=> s' → t βη-≡ t'
    → t / s βη-≡ t' / s'
/eq {t' = t'} s0 □ = cong/s s0 t'
/eq s0 (bsym y)  = bsym (/eq (=>sym s0) y)
/eq s0 (y ⟷ y') = /eq s0 y ⟷ cong/ y' _
/eq s0 (%Λ y)    = %Λ /eq (ss (cong-wkS vz s0) □) y
/eq s0 (y %· y') = /eq s0 y %· /eq s0 y'
/eq {s = s} {s' = s'} s0 (beta {t = t} {u = u})      =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ beta ⟩
     _ ⟷⟨ equiv (comm-/-/=> t (ss (wkS vz s) (var vz)) (ss ι (u / s))) ⟩
     _ ⟷⟨ cong/s (ss (=>≡ (wkS-extS/=> vz (u / s) s ι)) (cong/s s0 u)) t ⟩
     _ ⟷⟨ cong/s (ss (=>≡ (/=>ι s)) □) t ⟩
     _ ⟷⟨ cong/s (ss s0 □) t ⟩
     _ ⟷⟨ cong/s (ss (=>sym (=>≡ (ι/=> s'))) □) t ⟩
     _ ⟷⟨ bsym (equiv (comm-/-/=> t (ss ι u) s')) ⟩
     _ ∎
/eq s0 (eta {t = t}) =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ congΛ (congApp (equiv (wkExtS/ vz vz t _)) brefl) ⟩
     _ ⟷⟨ %Λ (%wkTm vz (cong/s s0 t) %· □) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

congUp : ∀ {Γ τ} → {t t' : ε ⊢ τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
congUp {ε} t0 = t0
congUp {y , y'} {_} {t} {t'} t0 = %wkTm vz (congUp {y} t0)

%close : ∀ {Γ Δ τ} {e e' : Γ ⊢ τ} → (s : Δ ⊂ Γ) → e βη-≡ e' 
       → close e s βη-≡ close e' s
%close ε eq = eq %/ sz
%close (cls y y') eq = eq %/ ss (⊂-=> y) (y' / ⊂-=> y)
%close (keep y) eq = eq %/ ss (wkS vz (⊂-=> y)) (var vz)
-}

\end{code}
%endif