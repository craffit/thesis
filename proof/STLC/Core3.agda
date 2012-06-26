--------------------------------------------------------------------------------
-- This module implements hereditary substitutions for the simply-typed       --
-- λ-calculus.                                                                --
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

{-# OPTIONS --termination-depth=6 #-}
-- {-# OPTIONS --no-termination-check #-}
module STLC.Core3 where


-- Simple types

infixr 6 _⇒_

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty


-- De Bruijn contexts

infixl 5 _,_

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

infixl 5 _+_

_+_ : Con → Con → Con
a + ε         = a
a + (y , y') = a + y , y'

-- De Bruijn indices (the set of variables)

infix 4 _∋_

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ σ} → Γ , σ ∋ σ
  vs : ∀ {τ Γ σ} → Γ ∋ σ → Γ , τ ∋ σ


-- Removing a variable from a context

infixl 5 _-_

_-_ : {σ : Ty} → (Γ : Con) → Γ ∋ σ → Con
ε       - ()
(Γ , σ) - vz     = Γ
(Γ , τ) - (vs x) = Γ - x , τ

infix 4 _⊑_
infixl 5 _▻_
data _⊑_ (Γ : Con) : Con → Set where
  refl :                                       Γ ⊑ Γ
  _▻_  : {Δ : Con} (Γ⊑Δ : Γ ⊑ Δ) (s : Ty)  →  Γ ⊑ Δ , s

-- Conversely, adding a variable to a context (weakening)

wkv : forall {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ∋ τ → Γ ∋ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)

wkv' : ∀ {Γ Δ τ} → Δ ⊑ Γ → Δ ∋ τ → Γ ∋ τ
wkv' refl       v = v
wkv' (Γ⊑Δ ▻ s) v = vs (wkv' Γ⊑Δ v) 

inject : {Γ Δ : Con} {s : Ty} → Δ ∋ s → Γ + Δ ∋ s
inject vz       = vz
inject (vs Δ∋x) = vs (inject Δ∋x)

makeVar : {Γ Δ : Con} {s : Ty} → Γ , s ⊑ Δ → Δ ∋ s
makeVar refl      = vz
makeVar (Γ⊑Δ ▻ _) = vs (makeVar Γ⊑Δ)

injectVar : ∀ {x Γ Δ ΓΔ⁺} → Γ + Δ ⊑ ΓΔ⁺ → Δ ∋ x → ΓΔ⁺ ∋ x
injectVar refl      Δ∋x = inject Δ∋x
injectVar (Γ⊑Δ ▻ _) Δ∋x = vs (injectVar Γ⊑Δ Δ∋x)

-- Extending a context

ext : ∀ {σ} → (Γ : Con) → Γ ∋ σ → Ty → Con
ext ε () τ
ext {σ} (y , .σ) vz τ   = (y , σ) , τ
ext (y , y') (vs y0) τ = ext y y0 τ , y'

extv : forall {Γ σ τ} → (x : Γ ∋ σ) → (t : Ty) → Γ ∋ τ → ext Γ x t ∋ τ
extv vz t s           = vs s
extv (vs y) t vz      = vz
extv (vs y) t (vs y') = vs (extv y t y')

-- The equality between variables: the predicate...

data EqV {Γ : Con} : {σ τ : Ty} → Γ ∋ σ → Γ ∋ τ → Set where
  same : forall {σ} → {x : Γ ∋ σ} → EqV {Γ} {σ} {σ} x x
  diff : forall {σ τ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → EqV {Γ} {σ} {τ} x (wkv x y)


-- ... and the function that decides it

eq : forall {Γ σ τ} → (x : Γ ∋ σ) → (y : Γ ∋ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)


-- The set of terms

infix  2  _⊢_
infixl 10 _·_

data _⊢_ : Con → Ty → Set where
  var  : ∀ {Γ σ} → Γ ∋ σ → Γ ⊢ σ
  Λ    : ∀ {Γ σ τ} → Γ , σ ⊢ τ → Γ ⊢ σ ⇒ τ
  _·_  : ∀ {Γ σ τ} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
  comb : ∀ {Γ τ} → ε ⊢ τ → Γ ⊢ τ

-- Weakening a term

wkTm : forall {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm {ε} () x
wkTm {ε , σ} vz x = comb x
wkTm {ε , σ} (vs ()) x
wkTm {a , b , σ} x (var v) = var (wkv x v)
wkTm {a , b , σ} x (Λ t) = Λ (wkTm (vs x) t)
wkTm {a , b , σ} x (t₁ · t₂) = wkTm x t₁ · wkTm x t₂
wkTm {a , b , σ} x (comb t) = comb t

wkTm' : forall {Δ Γ τ} → Δ ⊑ Γ → Δ ⊢ τ → Γ ⊢ τ
wkTm' refl t       = t
wkTm' (Γ⊑Δ ▻ s) t = wkTm vz (wkTm' Γ⊑Δ t)

--wkTm' : forall {Γ Δ τ} → 
up : ∀ {Γ τ} → ε ⊢ τ → Γ ⊢ τ
up {ε} v      = v
up {y , y'} v = wkTm vz (up {y} v)

-- Substitutions for variables and terms

substVar : forall {σ Γ τ} → Γ ∋ τ → (x : Γ ∋ σ) → Γ - x ⊢ σ → Γ - x ⊢ τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x

subst : forall {σ Γ τ} → Γ ⊢ τ → (x : Γ ∋ σ) → Γ - x ⊢ σ → Γ - x ⊢ τ
subst (var v) x u    = substVar v x u
subst (Λ t) x u      = Λ (subst t (vs x) (wkTm vz u))
subst (t₁ · t₂) x u   = subst t₁ x u · subst t₂ x u
subst (comb tm) x u  = comb tm

infix 5 _⟦·⟧_
{-
add⊑ : ∀ {Δ Γ Γ'} → Γ ⊑ Γ' → Γ + Δ ⊑ Γ' + Δ
add⊑ refl       = refl
add⊑ {Δ} (Γ⊑Δ ▻ s) = {!!}

lift⊑ : ∀ {Δ Γ Γ'} → Γ ⊑ Γ' → Δ + Γ ⊑ Δ + Γ'
lift⊑ {ε} eqv = {!!}
lift⊑ {y , y'} eqv = {!!}
-}
up' : ∀ {Γ σ τ} → ε , σ ⊢ τ → Γ , σ ⊢ τ
up' {ε} t = t
up' {y , y'} t = wkTm (vs vz) (up' {y} t)

mkComb : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
mkComb {ε} v               = comb v
mkComb {y , y'} (var y0)  = var y0
mkComb {y , y'} (Λ y0)    = Λ (mkComb y0)
mkComb {y , y'} (y0 · y1) = mkComb y0 · mkComb y1
mkComb {y , y'} (comb y0) = comb y0

unComb : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
unComb (var y)  = var y
unComb (Λ y)    = Λ (unComb y)
unComb (y · y') = unComb y · unComb y'
unComb (comb y) = {!!}

mutual
  _⟦·⟧_ : ∀ {Γ τ τ'} → Γ ⊢ τ ⇒ τ' → Γ ⊢ τ → Γ ⊢ τ'
--  comb f ⟦·⟧ a = --subst (up' f) vz a
  comb f     ⟦·⟧ comb a = comb (f · a)
  comb f     ⟦·⟧ a = comb f · a
  Λ f        ⟦·⟧ a = subst f vz a
  f          ⟦·⟧ a = f · a

--  _⟦comb⟧_ : ∀ {Γ τ τ'} → Γ ⊢ τ ⇒ τ' → Γ ⊢ τ → Γ ⊢ τ'
--  comb f ⟦comb⟧ comb a = comb (f ⟦·⟧ a)
--  comb f ⟦comb⟧ a      = up f ⟦·⟧ a
--  f      ⟦comb⟧ a      = f ⟦·⟧ a

  ⟦_⟧ : forall {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
  ⟦ var y ⟧   = var y
  ⟦ Λ y ⟧     = Λ ⟦ y ⟧
  ⟦ y · y' ⟧  = ⟦ y ⟧ ⟦·⟧ ⟦ y' ⟧
  ⟦ comb tm ⟧ = comb ⟦ tm ⟧
{-
⟦ comb tm ⟧ with ⟦ tm ⟧
⟦ comb tm ⟧ | comb tm' = comb tm'
⟦ comb tm ⟧ | tm'      = comb tm'-}