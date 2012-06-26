{-# OPTIONS --termination-depth=2 #-}
module STLC.Eval where

open import STLC.Base public
open import STLC.SSubst public

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

import Relation.Binary.EqReasoning
{-
congℕ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
congℕ f refl refl = refl
-}

-- Evaluation
mutual
  ⟦⟧app : ∀ {Γ τ σ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ⟦⟧app (Λ f) a     = f / sub vz a
  ⟦⟧app (var x) a   = app (var x) a
  ⟦⟧app (app f x) a = app (app f x) a

  ⟦_⟧ : ∀ {Γ τ} → Tm Γ τ → Tm Γ τ
  ⟦ var y ⟧    = var y
  ⟦ Λ y ⟧      = Λ ⟦ y ⟧
  ⟦ app y y' ⟧ = ⟦⟧app ⟦ y ⟧ ⟦ y' ⟧

v : ∀ {τ} → Tm ε (τ ⇒ τ)
v = ⟦ Λ (app (Λ (app (var vz) (app (var vz) (var (vs vz))))) (Λ (var vz))) ⟧
{-
wkTm-⟦⟧app :  ∀ {Γ τ σ a} → (v : Var Γ a) → (y : Tm (Γ - v) (σ ⇒ τ)) → (y' : Tm (Γ - v) σ) 
              → wkTm v (⟦⟧app y y') ≡ ⟦⟧app (wkTm v y) (wkTm v y')
wkTm-⟦⟧app v (var y) y' = refl
wkTm-⟦⟧app v (Λ y) y' 
    = ≡begin
    _ ≡⟨ sym (wkSI/ (vs v) v y (ss ι y')) ⟩
    _ ≡⟨ cong (λ p → wkTm (vs v) y / ss p (wkTm v y')) (wkSI-ι v) ⟩

    _ ≡∎
wkTm-⟦⟧app v (app y y') y0 = refl

wkTm-⟦⟧ : ∀ {Γ τ σ} → (v : Var Γ σ) → (t : Tm (Γ - v) τ) → wkTm v ⟦ t ⟧ ≡ ⟦ wkTm v t ⟧
wkTm-⟦⟧ v (var y)    = refl
wkTm-⟦⟧ v (Λ y)      = cong Λ (wkTm-⟦⟧ (vs v) y)
wkTm-⟦⟧ v (app y y') 
  = ≡begin
  _ ≡⟨ wkTm-⟦⟧app v ⟦ y ⟧ ⟦ y' ⟧ ⟩
  _ ≡⟨ cong₂ ⟦⟧app (wkTm-⟦⟧ v y) (wkTm-⟦⟧ v y') ⟩
  _ ≡∎

⟦_⟧/ : ∀ {Γ Δ} → Γ => Δ → Γ => Δ
⟦ sz ⟧/      = sz
⟦ ss y y' ⟧/ = ss ⟦ y ⟧/ ⟦ y' ⟧

wkS-⟦⟧/ : ∀ {Γ Δ τ} → (v : Var Δ τ) → (s : Γ => Δ - v) → wkS v ⟦ s ⟧/ ≡ ⟦ wkS v s ⟧/
wkS-⟦⟧/ v sz        = refl
wkS-⟦⟧/ v (ss y y') = cong₂ ss (wkS-⟦⟧/ v y) (wkTm-⟦⟧ v y')

lookup-⟦⟧/ : ∀ {Γ Δ τ} → (v : Var Γ τ) → (s : Γ => Δ) → lookup v ⟦ s ⟧/ ≡ ⟦ lookup v s ⟧
lookup-⟦⟧/ vz (ss y y')      = refl
lookup-⟦⟧/ (vs y) (ss y' y0) = lookup-⟦⟧/ y y'

⟦⟧/-comm : ∀ {Γ Δ τ} → (t : Tm Γ τ) → (s : Γ => Δ) → ⟦ t / s ⟧ ≡ ⟦ t ⟧ / ⟦ s ⟧/
⟦⟧/-comm (var y) s    = sym (lookup-⟦⟧/ y s)
⟦⟧/-comm (Λ y) s 
  = ≡begin
  _ ≡⟨ cong Λ (⟦⟧/-comm y (ss (wkS vz s) (var vz))) ⟩
  _ ≡⟨ cong (λ p → Λ (⟦ y ⟧ / ss p (var vz))) (sym (wkS-⟦⟧/ vz s)) ⟩
  _ ≡∎
⟦⟧/-comm (app y y') s
  = ≡begin
  _ ≡⟨ cong₂ ⟦⟧app (⟦⟧/-comm y s) (⟦⟧/-comm y' s) ⟩
  _ ≡⟨ {!!} ⟩
  _ ≡∎
  

mutual
  ⟦⟧/ : ∀ {Γ σ τ} → (y : Tm (Γ , σ) τ) → (a : Tm Γ σ) → ⟦ y / ss ι a ⟧ ≡ ⟦ y ⟧ / ss ι ⟦ a ⟧
  ⟦⟧/ (var y) v = {!!}
  ⟦⟧/ (Λ y) v = {!!}
  ⟦⟧/ (app y y') v = {!!}

  ⟦⟧app-lem : ∀ {Γ τ σ} → (f : Tm Γ (σ ⇒ τ)) → (a : Tm Γ σ) →  ⟦ ⟦⟧app f a ⟧ ≡ ⟦⟧app ⟦ f ⟧ ⟦ a ⟧
  ⟦⟧app-lem (var y) a    = refl
  ⟦⟧app-lem (Λ y) a      = {!!}
  ⟦⟧app-lem (app y y') a = {!cong (λ v → app (app y y') v) (⟦⟧involutive a)!}
  
  ⟦⟧involutive : ∀ {Γ τ} → (t : Tm Γ τ) → ⟦ ⟦ t ⟧ ⟧ ≡ ⟦ t ⟧
  ⟦⟧involutive (var y) = refl
  ⟦⟧involutive (Λ y) = cong Λ (⟦⟧involutive y)
  ⟦⟧involutive (app y y') = {!!}

-}
-- βη-equality

infix 1 _βη-≡_

data _βη-≡_ {Γ : Con} : {σ : Ty} → Tm Γ σ → Tm Γ σ → Set where
  brefl : forall {σ} → {t : Tm Γ σ} → t βη-≡ t
  bsym : forall {σ} → {t₁ t₂ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  btrans : forall {σ} → {t₁ t₂ t₃ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  congΛ : forall {σ τ} → {t₁ t₂ : Tm (Γ , σ) τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  congApp : forall {σ τ} → {t₁ t₂ : Tm Γ (σ ⇒ τ)} → {u₁ u₂ : Tm Γ σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₁ βη-≡ app t₂ u₂
  beta : forall {σ τ} → {t : Tm (Γ , σ) τ} → {u : Tm Γ σ} → app (Λ t) u βη-≡ (t / sub vz u)
  eta : forall {σ τ} → {t : Tm Γ (σ ⇒ τ)} → Λ (app (wkTm vz t) (var vz)) βη-≡ t

open import Relation.Binary hiding (_⇒_)

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
-- open ≡-Reasoning

βηsetoid : {Γ : Con} {σ : Ty} → Setoid _ _
βηsetoid {Γ} {σ} = 
  record { Carrier = Tm Γ σ 
         ; _≈_ = _βη-≡_
         ; isEquivalence = 
              record { refl  = brefl
                     ; sym   = bsym
                     ; trans = btrans
                     }                              
         }

-- Congruences of βη-≡

equiv : forall {Γ σ} → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
equiv refl = brefl


congSubstVar : forall {σ Γ τ} → (v : Var Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl


congWkTm : forall {Γ σ τ} → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm _ brefl = brefl
congWkTm x (bsym p) = bsym (congWkTm x p)
congWkTm x (btrans p₁ p₂) = btrans (congWkTm x p₁) (congWkTm x p₂)
congWkTm x (congΛ p) = congΛ (congWkTm (vs x) p)
congWkTm x (congApp p₁ p₂) = congApp (congWkTm x p₁) (congWkTm x p₂)
congWkTm x {app (Λ t) u} beta = btrans beta 
  (equiv 
    ( ≡begin
    _ ≡⟨ sym (subst/ vz (wkTm (vs x) t) (wkTm x u)) ⟩
    _ ≡⟨ sym (wkTmSubstExc (vs x) t vz u) ⟩
    _ ≡⟨ cong (\p → wkTm x p) (subst/ vz t u) ⟩    
    _ ≡∎
    )
  )
congWkTm x {._} {t} eta = btrans (congΛ (congApp (equiv (wkTmExc vz x t)) brefl)) eta


congSubst : forall {σ Γ τ} → (t : Tm Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → subst t x u₁ βη-≡ subst t x u₂
congSubst (var v) x p = congSubstVar v x p
congSubst (Λ t) x p = congΛ (congSubst t (vs x) (congWkTm vz p))
congSubst (app t₁ t₂) x p = congApp (congSubst t₁ x p) (congSubst t₂ x p)

congUp : forall {Γ τ} → {t t' : Tm ε τ} → t βη-≡ t' → up {Γ} t βη-≡ up {Γ} t'
congUp {ε} t0 = t0
congUp {y , y'} {_} {t} {t'} t0 = congWkTm vz (congUp {y} t0)

cong/ : ∀ {Γ Δ τ} → {t t' : Tm Γ τ} → t βη-≡ t' → (s : Γ => Δ) → (t / s) βη-≡ (t' / s)
cong/ brefl s = brefl
cong/ (bsym y) s = bsym (cong/ y s)
cong/ (btrans y y') s = btrans (cong/ y s) (cong/ y' s)
cong/ (congΛ y) s = congΛ (cong/ y (ss (wkS vz s) (var vz)))
cong/ (congApp y y') s = congApp (cong/ y s) (cong/ y' s)
cong/ (beta {_} {_} {t} {u}) s =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ bsym (equiv (dist-sub vz t vz (u / s) s)) ⟩
       _ ⟷⟨ equiv (cong (λ p → p / ss s (u / s)) (sym (ι/ t))) ⟩
       _ ⟷⟨ bsym (equiv (comm-/ vz t vz u ι s)) ⟩
       _ ∎
cong/ (eta {_} {_} {t}) s =    
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ congΛ (congApp (equiv (wkSI/ vz vz t s)) brefl) ⟩
       _ ⟷⟨ eta ⟩
       _ ∎
-- Proofs that involve with

substSame : forall {Γ σ} → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → eq x x ≡ same → u βη-≡ substVar x x u
substSame x u p with eq x x
substSame x u refl | .same = brefl


substDiff : forall {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (u : Tm (Γ - x) σ) → eq x (wkv x y) ≡ diff x y → var y βη-≡ substVar (wkv x y) x u
substDiff x y u p with eq x (wkv x y)
substDiff x y u refl | .(diff x y) = brefl

⟦⟧appβη : ∀ {Γ τ τ'} → (t : Tm Γ (τ ⇒ τ')) → (t' : Tm Γ τ) → app t t' βη-≡ ⟦⟧app t t'
⟦⟧appβη (Λ y) a      = beta
⟦⟧appβη (var y) a    = brefl
⟦⟧appβη (app y y') a = brefl

evalβη : ∀ {Γ τ} → (t : Tm Γ τ) → t βη-≡ ⟦ t ⟧
evalβη (var y)  = brefl
evalβη (Λ y)    = congΛ (evalβη y)
evalβη (app y y') =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
         app y y'
       ⟷⟨ congApp (evalβη y) (evalβη y') ⟩
         app ⟦ y ⟧ ⟦ y' ⟧
       ⟷⟨ ⟦⟧appβη ⟦ y ⟧ ⟦ y' ⟧ ⟩
         ⟦ app y y' ⟧
       ∎

β≡ : ∀ {Γ τ} → {t t' : Tm Γ τ} → ⟦ t ⟧ βη-≡ ⟦ t' ⟧ → t βη-≡ t'
β≡ {_} {_} {t} {t'} eqp =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
         t
       ⟷⟨ evalβη t ⟩
         ⟦ t ⟧
       ⟷⟨ eqp ⟩
         ⟦ t' ⟧
       ⟷⟨ bsym (evalβη t') ⟩
         t'
       ∎

