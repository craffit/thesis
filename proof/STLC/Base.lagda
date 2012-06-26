\begin{code}
--------------------------------------------------------------------------------
-- The module implements:                                                     --
--   - a predicate that defines the βη-equivalence on terms                   --
--   - the most important theorems about hereditary substitutions we prove:   --
--     completeness, soundness and stability. Completeness and soundness      --
--     that the βη-equivalence is decidable, and the normalizer defined with  --
--     the aid of hereditary substitutions decides the βη-equivalence.        --
--------------------------------------------------------------------------------

    -- This program is free software: you can redistribute it and/or modify
    -- it under the terms of the GNU General Public License as published by
    -- the Free Software Foundation, either version 3 of the License, or
    -- (at your option) any later version.

    -- This program is distributed in the hope that it will be useful,
    -- but WITHOUT ANY WARRANTY; without even the implied warranty of
    -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    -- GNU General Public License for more details.

    -- You should have received a copy of the GNU General Public License
    -- along with this program.  If not, see <http://www.gnu.org/licenses/>.

    -- Copyright Thorsten Altenkirch and Chantal Keller, 2010

module STLC.Base where


-- Simple types
infixr 4 _⇒_

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty


-- De Bruijn contexts

infixl 3 _,_

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con


-- De Bruijn indices (the set of variables)

data Var : Con → Ty → Set where
  vz : forall {Γ σ} → Var (Γ , σ) σ
  vs : forall {τ Γ σ} → Var Γ σ → Var (Γ , τ) σ


-- Removing a variable from a context

_-_ : {σ : Ty} → (Γ : Con) → Var Γ σ → Con
ε       - ()
(Γ , σ) - vz     = Γ
(Γ , τ) - (vs x) = (Γ - x) , τ


-- Conversely, adding a variable to a context (weakening)

wkv : forall {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)


-- The equality between variables: the predicate...

data EqV {Γ : Con} : {σ τ : Ty} → Var Γ σ → Var Γ τ → Set where
  same : forall {σ} → {x : Var Γ σ} → EqV {Γ} {σ} {σ} x x
  diff : forall {σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → EqV {Γ} {σ} {τ} x (wkv x y)


-- ... and the function that decides it

eq : forall {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)

-- The set of terms
infixl 3 app

data Tm : Con → Ty → Set where
  var : forall {Γ σ} → Var Γ σ → Tm Γ σ
  Λ   : forall {Γ σ τ} → Tm (Γ , σ) τ → Tm Γ (σ ⇒ τ)
  app : forall {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ

infixl 3 _·_

_·_ : forall {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
_·_ = app

infix 1 _⊢_

_⊢_ : Con → Ty → Set
_⊢_ = Tm

-- Weakening a term

wkTm : forall {σ Γ τ} → (x : Var Γ σ) → Tm (Γ - x) τ → Tm Γ τ
wkTm x (var v) = var (wkv x v)
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

weaken : ∀ {Γ τ σ} → Tm Γ τ → Tm (Γ , σ) τ
weaken t = wkTm vz t

up : ∀ {Γ τ} → Tm ε τ → Tm Γ τ
up {ε} t = t
up {y , y'} t = weaken (up {y} t)

-- Substitutions for variables and terms

substVar : forall {σ Γ τ} → Var Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x


subst : forall {σ Γ τ} → Tm Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
subst (var v) x u = substVar v x u
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
open ≡-Reasoning

-- Proofs that involve with

substSame2 : forall {Γ σ τ} → (x : Var Γ σ) → eq x x ≡ same → eq (vs {τ} x) (vs x) ≡ same
substSame2 x p with eq x x
substSame2 x refl | .same = refl


substSame3 : forall {Γ σ} → (x : Var Γ σ) → eq x x ≡ same
substSame3 vz = refl
substSame3 (vs x) = substSame2 x (substSame3 x)


substDiff2 : forall {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
substDiff2 x y p with eq x (wkv x y)
substDiff2 x y refl | .(diff x y) = refl


substDiff3 : forall {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y
substDiff3 vz y = refl
substDiff3 (vs x) vz = refl
substDiff3 (vs x) (vs y) = substDiff2 x y (substDiff3 x y)


-- Changing the context in which a variable is typed

!_>₀_ : forall {Γ Δ σ} → Γ ≡ Δ → Var Γ σ → Var Δ σ
! refl >₀ v = v


-- Commutation between var constructors and !_>₀_

!vz : forall {Γ Δ σ} → (p : Γ ≡ Δ) → ! cong (λ Θ → Θ , σ) p >₀ vz ≡ vz
!vz refl = refl


!vs : forall {Γ Δ σ τ} → (p : Γ ≡ Δ) → (x : Var Γ τ) → ! cong (λ Θ → Θ , σ) p >₀ (vs x) ≡ vs (! p >₀ x)
!vs refl _ = refl


-- Another commutation

!! : forall {Γ Δ σ} → (x : Var Γ σ) → (y : Var Δ σ) → (p : Γ ≡ Δ) → x ≡ ! sym p >₀ y → y ≡ ! p >₀ x
!! x .x refl refl = refl


-- Changing the proof

!p : forall {Γ Δ σ} → (v : Var Γ σ) → (p q : Γ ≡ Δ) → p ≡ q → ! p >₀ v ≡ ! q >₀ v
!p v p .p refl = refl


-- Changing the context in which a term is typed
!_>₁_ : forall {Γ Δ σ} → Γ ≡ Δ → Tm Γ σ → Tm Δ σ
! refl >₁ t = t


-- Commutation between term constructors and !_>₁_

!var : forall {Γ Δ σ} → (p : Γ ≡ Δ) → (v : Var Γ σ) → ! p >₁ var v ≡ var (! p >₀ v)
!var refl _ = refl


!Λ : forall {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t : Tm (Γ , σ) τ) → ! p >₁ Λ t ≡ Λ (! cong (λ Θ → Θ , σ) p >₁ t)
!Λ refl _ = refl


!app : forall {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t₁ : Tm Γ (σ ⇒ τ)) → (t₂ : Tm Γ σ) → ! p >₁ app t₁ t₂ ≡ app (! p >₁ t₁) (! p >₁ t₂)
!app refl _ _ = refl


-- Commutation between wkTm and !_>₁_

!wkTm : forall {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Tm Γ τ) → ! cong (λ Θ → Θ , σ) p >₁ wkTm vz u ≡ wkTm vz (! p >₁ u)
!wkTm refl _ = refl


-- Changing term inside !_>₁_

!≡₁ : forall {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → ! p >₁ t₁ ≡ ! p >₁ t₂
!≡₁ _ refl = refl


-- Injectivity of vs and wkv

tyInj-left : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → a ≡ b
tyInj-left refl = refl 

tyInj-right : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → c ≡ d
tyInj-right refl = refl 

vsInj : forall {τ Γ σ} → (i j : Var Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj i .i refl = refl


wkvInj : forall {Γ σ τ} → (k : Var Γ σ) → (i j : Var (Γ - k) τ) → wkv k i ≡ wkv k j → i ≡ j
wkvInj vz vz vz p = refl
wkvInj vz vz (vs j) ()
wkvInj vz (vs i) vz ()
wkvInj vz (vs i) (vs j) p = vsInj (vs i) (vs j) p
wkvInj (vs k) vz vz p = refl
wkvInj (vs k) vz (vs j) ()
wkvInj (vs k) (vs i) vz ()
wkvInj (vs k) (vs i) (vs j) p = cong vs (wkvInj k i j (vsInj (wkv k i) (wkv k j) p))


-- Basic lemma

reflExtConSym : forall {Γ Δ : Con} → (σ : Ty) → (p : Γ ≡ Δ) → sym {_} {Con} (cong (λ Θ → Θ , σ) p) ≡ cong (λ Θ → Θ , σ) (sym p)
reflExtConSym _ refl = refl


vsWkvEq : forall {Γ σ τ} → (z x : Var (Γ , τ) σ) → vs z ≡ wkv (vs vz) x → z ≡ x
vsWkvEq z vz ()
vsWkvEq z (vs x) p = vsInj z (vs x) p

rem : forall {Γ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ) -> Var (Γ - (wkv x y)) σ
rem vz _ = vz
rem (vs x) vz = x
rem (vs x) (vs y) = vs (rem x y)


-- Lemmas about rem

conExc : forall {Γ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ) -> (Γ - x) - y ≡ (Γ - (wkv x y)) - (rem x y)
conExc vz y = refl
conExc (vs x) vz = refl
conExc (vs {σ} x) (vs y) = cong (λ Θ → Θ , σ) (conExc x y)


wkRem : forall {Γ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ) -> wkv (wkv x y) (rem x y) ≡ x
wkRem vz _ = refl
wkRem (vs _) vz = refl
wkRem (vs x) (vs y) = cong vs (wkRem x y)


wkvExc : forall {ρ Γ σ τ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ) -> (v : Var ((Γ - x) - y) ρ) -> wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ wkv x (wkv y v)
wkvExc vz _ _ = refl
wkvExc (vs x) vz _ = refl
wkvExc (vs x) (vs y) vz =  cong (λ v → wkv (vs (wkv x y)) (wkv (vs (rem x y)) v)) (!vz (conExc x y))
wkvExc (vs x) (vs y) (vs v) = begin
  _ ≡⟨ cong (λ z → wkv (vs (wkv x y)) (wkv (vs (rem x y)) z)) (!vs (conExc x y) v) ⟩
  _ ≡⟨ cong vs (wkvExc x y v) ⟩
  _ ∎


wkTmExc : forall {Γ σ τ ρ} -> (x : Var Γ σ) -> (y : Var (Γ - x) τ) -> (t : Tm ((Γ - x) - y) ρ) -> wkTm (wkv x y) (wkTm (rem x y) (! conExc x y >₁ t)) ≡ wkTm x (wkTm y t)
wkTmExc x y (var v) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!var (conExc x y) v) ⟩
  _ ≡⟨ cong var (wkvExc x y v) ⟩
  _ ∎
wkTmExc x y (Λ t) = begin
  _ ≡⟨ cong (λ u → wkTm (wkv x y) (wkTm (rem x y) u)) (!Λ (conExc x y) t) ⟩
  _ ≡⟨ cong Λ (wkTmExc (vs x) (vs y) t) ⟩
  _ ∎
wkTmExc x y (app t₁ t₂) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!app (conExc x y) t₁ t₂) ⟩
  _ ≡⟨ cong₂ app (wkTmExc x y t₁) (wkTmExc x y t₂) ⟩
  _ ∎

wkvSubstExtAux1 : forall {Γ σ τ} -> (y : Var Γ σ) -> (v : Var (Γ - y) τ) -> (u : Tm ((Γ - y) - v) τ) -> eq (wkv y v) (wkv y v) ≡ same -> wkTm (rem y v) (! conExc y v >₁ u) ≡ substVar (wkv y v) (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux1 y v u p with eq (wkv y v) (wkv y v)
wkvSubstExtAux1 y v u refl | .same = refl


wkvSubstExtAux2 : forall {Γ σ τ ρ} -> (y : Var Γ σ) -> (v : Var (Γ - y) ρ) -> (z : Var ((Γ - y) - v) τ) -> (u : Tm ((Γ - y) - v) ρ) -> eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ≡ diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)) -> wkTm (rem y v) (! conExc y v >₁ var z) ≡ substVar (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
  (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux2 y v z u p with eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
wkvSubstExtAux2 y v z u refl
  | .(diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) = (cong (wkTm (rem y v)) (!var (conExc y v) z))


wkvSubstExt : forall {Γ σ τ ρ} -> (y : Var Γ σ) -> (v : Var (Γ - y) τ) -> (x : Var (Γ - y) ρ) -> (u : Tm ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (substVar v x u)) ≡ substVar (wkv y v) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkvSubstExt y v x u with eq x v
wkvSubstExt y v .v u | same = wkvSubstExtAux1 y v u (substSame3 (wkv y v))
wkvSubstExt y .(wkv v z) .v u | diff v z = begin
  _ ≡⟨ wkvSubstExtAux2 y v z u (substDiff3 (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ⟩
  _ ≡⟨ cong (λ a → substVar a (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))) (wkvExc y v z) ⟩
  _ ∎


wkTmSubstExc : forall {Γ σ τ ρ} -> (y : Var Γ σ) -> (t : Tm (Γ - y) τ) -> (x : Var (Γ - y) ρ) -> (u : Tm ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (subst t x u)) ≡ subst (wkTm y t) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTmSubstExc y (var v) x u = wkvSubstExt y v x u
wkTmSubstExc y (Λ t) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!Λ (conExc y x) (subst t (vs x) (wkTm vz u))) ⟩
  _ ≡⟨ cong Λ (wkTmSubstExc (vs y) t (vs x) (wkTm vz u)) ⟩
  _ ≡⟨ cong (λ n → Λ (subst (wkTm (vs y) t) (vs (wkv y x)) (wkTm (vs (rem y x)) n))) (!wkTm (conExc y x) u) ⟩
  _ ≡⟨ cong (λ n → Λ (subst (wkTm (vs y) t) (vs (wkv y x)) n)) (wkTmExc vz (rem y x) (! conExc y x >₁ u)) ⟩
  _ ∎
wkTmSubstExc y (app t₁ t₂) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!app (conExc y x) (subst t₁ x u) (subst t₂ x u)) ⟩
  _ ≡⟨ cong₂ app (wkTmSubstExc y t₁ x u) (wkTmSubstExc y t₂ x u) ⟩
  _ ∎

weakSubstAux : forall {Γ σ τ} -> (x : Var Γ τ) -> (v : Var (Γ - x) σ) -> (u : Tm (Γ - x) τ) -> eq x (wkv x v) ≡ diff x v -> substVar (wkv x v) x u ≡ var v
weakSubstAux x v u p with eq x (wkv x v)
weakSubstAux x v u refl | .(diff x v) = refl


weakSubst : forall {Γ σ τ} -> (x : Var Γ τ) -> (t : Tm (Γ - x) σ) -> (u : Tm (Γ - x) τ) -> subst (wkTm x t) x u ≡ t
weakSubst x (var v) u = weakSubstAux x v u (substDiff3 x v)
weakSubst x (Λ t) u = cong Λ (weakSubst (vs x) t (wkTm vz u))
weakSubst x (app t₁ t₂) u = cong₂ app (weakSubst x t₁ u) (weakSubst x t₂ u)


-- Commutation lemmas between substVar and rem, wkv

substVarCommAux2 : forall {Γ σ τ} -> (x : Var Γ σ) -> (u₁ : Tm (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Tm ((Γ - x) - y) τ) -> eq (rem x y) (rem x y) ≡ same -> ! conExc x y >₁ subst u₁ y u₂ ≡ substVar (rem x y) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux2 x u₁ y u₂ p with eq (rem x y) (rem x y)
substVarCommAux2 x u₁ y u₂ refl | .same = refl


substVarCommAux1 : forall {Γ σ τ} -> (x : Var Γ σ) -> (u₁ : Tm (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Tm ((Γ - x) - y) τ) -> eq (wkv x y) (wkv (wkv x y) (rem x y)) ≡ diff (wkv x y) (rem x y) -> ! conExc x y >₁ subst u₁ y u₂ ≡ subst (substVar (wkv (wkv x y) (rem x y)) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux1 x u₁ y u₂ p with eq (wkv x y) (wkv (wkv x y) (rem x y))
substVarCommAux1 x u₁ y u₂ refl | .(diff (wkv x y) (rem x y)) = substVarCommAux2 x u₁ y u₂ (substSame3 (rem x y))


substVarCommAux4 : forall {Γ σ τ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) σ) -> (u₂ : Tm ((Γ - x) - y) σ) -> eq (wkv x y) (wkv x y) ≡ same -> ! conExc x y >₁ u₂ ≡ subst (substVar (wkv x y) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux4 x u₁ y u₂ p with eq (wkv x y) (wkv x y)
substVarCommAux4 x u₁ y u₂ refl | .same = sym (weakSubst (rem x y) (! conExc x y >₁ u₂) (! conExc x y >₁ subst u₁ y u₂))


substVarCommAux6 : forall {Γ σ τ ρ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ diff (rem x y) (! conExc x y >₀ v) -> ! conExc x y >₁ var v ≡ substVar (wkv (rem x y) (! conExc x y >₀ v)) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux6 x u₁ y u₂ v p with  eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v))
substVarCommAux6 x u₁ y u₂ v refl | .(diff (rem x y) (! conExc x y >₀ v)) = !var (conExc x y) v


substVarCommAux5 : forall {Γ σ τ ρ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ≡ diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) -> ! conExc x y >₁ var v ≡ subst (substVar (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux5 x u₁ y u₂ v p with eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)))
substVarCommAux5 x u₁ y u₂ v refl | .(diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) = substVarCommAux6 x u₁ y u₂ v
                                                                                                (substDiff3 (rem x y) (! conExc x y >₀ v))


substVarCommAux3 : forall {Γ σ τ ρ} -> (x : Var Γ τ) -> (v : Var (Γ - x) σ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ (substVar v y u₂) ≡ subst (substVar (wkv x v) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux3 x v u₁ y u₂ with eq y v
substVarCommAux3 x y u₁ .y u₂ | same = substVarCommAux4 x u₁ y u₂ (substSame3 (wkv x y))
substVarCommAux3 x .(wkv y v) u₁ .y u₂ | diff y v = begin
  _ ≡⟨ substVarCommAux5 x u₁ y u₂ v (substDiff3 (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ⟩
  _ ≡⟨ cong (λ z → subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)) (wkvExc x y v) ⟩
  _ ∎


substVarComm : forall {Γ σ τ ρ} -> (v : Var Γ σ) -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ subst (substVar v x u₁) y u₂ ≡ subst (substVar v (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarComm v x u₁ y u₂ with eq x v
substVarComm x .x u₁ y u₂ | same = begin
  _ ≡⟨ substVarCommAux1 x u₁ y u₂ (substDiff3 (wkv x y) (rem x y)) ⟩
  _ ≡⟨ cong (λ z → subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)) (wkRem x y) ⟩
  _ ∎
substVarComm .(wkv x v) .x u₁ y u₂ | diff x v = substVarCommAux3 x v u₁ y u₂


substComm : forall {σ Γ τ ρ} -> (t : Tm Γ σ) -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ subst (subst t x u₁) y u₂ ≡ subst (subst t (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substComm (var v) x u₁ y u₂ = substVarComm v x u₁ y u₂
substComm {σ ⇒ _} (Λ t) x u₁ y u₂ = begin
  _ ≡⟨ !Λ (conExc x y) (subst (subst t (vs x) (wkTm vz u₁)) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong Λ (substComm t (vs x) (wkTm vz u₁) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm (vs (rem x y)) u)) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (!wkTm (conExc x y) u₂) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) u) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (wkTmExc vz (rem x y) (! conExc x y >₁ u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!≡₁ (cong (λ Θ → Θ , σ) (conExc x y)) (sym (wkTmSubstExc vz u₁ y u₂))) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!wkTm (conExc x y) (subst u₁ y u₂)) ⟩
  _ ∎
substComm (app t₁ t₂) x u₁ y u₂ = begin
  _ ≡⟨ !app (conExc x y) (subst (subst t₁ x u₁) y u₂) (subst (subst t₂ x u₁) y u₂) ⟩
  _ ≡⟨ cong₂ app (substComm t₁ x u₁ y u₂) (substComm t₂ x u₁ y u₂) ⟩
  _ ∎

commWkUp : ∀ {Γ τ σ} → (x : Var Γ σ) → (t : Tm ε τ) → up {Γ} t ≡ wkTm x (up {Γ - x} t)
commWkUp {ε} () t
commWkUp {y , σ} vz t       = refl
commWkUp {y , y'} (vs y0) t =
  let open ≡-Reasoning 
  in begin
       wkTm vz (up t)
     ≡⟨ cong (λ i → wkTm vz i) (commWkUp y0 t) ⟩
       _
     ≡⟨ wkTmExc (vs y0) vz (up t) ⟩
       wkTm (vs y0) (wkTm vz (up t))
     ∎

-- up-Λ : ∀ {Δ τ σ} → (f : Tm ε (σ ⇒ τ)) → (a : Tm ε σ) → up (Λ f) ≡ Λ up {Δ} (app f a)
up-app : ∀ {Δ τ σ} → (f : Tm ε (σ ⇒ τ)) → (a : Tm ε σ) → app (up f) (up a) ≡ up {Δ} (app f a)
up-app {ε} f a = refl
up-app {y , y'} f a = cong (\v → wkTm vz v) (up-app f a)

subst-up : ∀ {Γ} {τ σ} → (t : Tm ε τ) → (v : Var Γ σ) → (u : Tm (Γ - v) σ) → subst (up {Γ} t) v u ≡ up t
subst-up {Γ} t v u =
  let open ≡-Reasoning
  in begin
       subst (up t) v u
     ≡⟨ cong (λ i → subst i v u) (commWkUp v t) ⟩
       subst (wkTm v (up t)) v u
     ≡⟨ weakSubst v (up t) u ⟩
       up t
     ∎\end{code}
