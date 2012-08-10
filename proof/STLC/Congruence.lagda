\begin{code}
module STLC.Congruence where

open import STLC.Base
open import STLC.Up
open import STLC.Equality
open import STLC.Syntax
open import STLC.SSubst
open import Data.Nat

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)

infix 1 _≡τ_

infix 1 _≡Γ_

data _≡τ_ : (τ : Ty) → (τ' : Ty) → Set where
  ○     : ○ ≡τ ○
  C     : (y : ℕ) → C y ≡τ C y
  _⇒_   : ∀ {τ σ τ' σ'} → (p1 : τ ≡τ τ') → (p2 : σ ≡τ σ') → τ ⇒ σ ≡τ τ' ⇒ σ'


⟦_⟧≡τ : {τ τ' : Ty} → τ ≡τ τ' → τ ≡ τ'
⟦ ○ ⟧≡τ = refl
⟦ C y ⟧≡τ = refl
⟦ p1 ⇒ p2 ⟧≡τ = cong₂ _⇒_ ⟦ p1 ⟧≡τ ⟦ p2 ⟧≡τ

_↑≡τ : {τ τ' : Ty} → τ ≡ τ' → τ ≡τ τ'
_↑≡τ {.○} {○} refl = ○
_↑≡τ {.(C y)} {C y} refl = C y
_↑≡τ {.(y ⇒ y')} {y ⇒ y'} refl = refl ↑≡τ ⇒ refl ↑≡τ 

≡τrefl : {τ : Ty} → τ ≡τ τ
≡τrefl {○} = ○
≡τrefl {C y} = C y
≡τrefl {y ⇒ y'} = ≡τrefl ⇒ ≡τrefl

≡τsym : {τ τ' : Ty} → τ ≡τ τ' → τ' ≡τ τ
≡τsym ○ = ○
≡τsym (C y) = C y
≡τsym (p1 ⇒ p2) = ≡τsym p1 ⇒ ≡τsym p2

≡τtrans : {τ τ' τ'' : Ty} → τ ≡τ τ' → τ' ≡τ τ'' → τ ≡τ τ''
≡τtrans ○ p2 = p2
≡τtrans (C y) p2 = p2
≡τtrans (p1 ⇒ p2) (p3 ⇒ p4) = ≡τtrans p1 p3 ⇒ ≡τtrans p2 p4

⟦⟧≡τ-id : {τ τ' : Ty} → (x : τ ≡ τ') → ⟦ x ↑≡τ ⟧≡τ ≡ x
⟦⟧≡τ-id {.○} {○} refl = refl
⟦⟧≡τ-id {.(C y)} {C y} refl = refl
⟦⟧≡τ-id {.(y ⇒ y')} {y ⇒ y'} refl = cong₂ (cong₂ _⇒_) (⟦⟧≡τ-id {y} {y} refl) (⟦⟧≡τ-id {y'} {y'} refl)

≡τ-eq-refl : {τ : Ty} → (x : τ ≡τ τ) → x ≡ ≡τrefl
≡τ-eq-refl ○ = refl
≡τ-eq-refl (C y) = refl
≡τ-eq-refl (p1 ⇒ p2) = cong₂ _⇒_ (≡τ-eq-refl p1) (≡τ-eq-refl p2)

≡τ-eq-eq : ∀ {τ τ'} → (p p2 : τ ≡τ τ') → p ≡ p2
≡τ-eq-eq p p2 with ⟦ p ⟧≡τ
... | refl = trans (≡τ-eq-refl p) (sym (≡τ-eq-refl p2))

-- ≡τ-sym-trans : 
data _≡Γ_ : (Γ : Con) → (Δ : Con) → Set where
  ε     : ε ≡Γ ε
  _,_   : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → Γ , τ ≡Γ Δ , σ

⟦_⟧≡Γ : ∀ {Γ Δ} → Γ ≡Γ Δ → Γ ≡ Δ
⟦ ε ⟧≡Γ = refl
⟦ p1 , p2 ⟧≡Γ = cong₂ _,_ ⟦ p1 ⟧≡Γ ⟦ p2 ⟧≡τ

_↑≡Γ : ∀ {Γ Δ} → Γ ≡ Δ → Γ ≡Γ Δ
_↑≡Γ {.ε} {ε} refl = ε
_↑≡Γ {.(y , y')} {y , y'} refl = refl ↑≡Γ , refl ↑≡τ

≡Γrefl : ∀ {Γ} → Γ ≡Γ Γ
≡Γrefl {ε} = ε
≡Γrefl {y , y'} = ≡Γrefl , ≡τrefl

≡Γsym : ∀ {Γ Δ} → Γ ≡Γ Δ → Δ ≡Γ Γ
≡Γsym ε = ε
≡Γsym (p1 , p2) = ≡Γsym p1 , ≡τsym p2

≡Γtrans : {Γ Δ Δ' : Con} → Γ ≡Γ Δ → Δ ≡Γ Δ' → Γ ≡Γ Δ'
≡Γtrans ε ε = ε
≡Γtrans (p1 , p2) (p3 , p4) = ≡Γtrans p1 p3 , ≡τtrans p2 p4

⟦⟧≡Γ-id : {Γ Δ : Con} → (x : Γ ≡ Δ) → ⟦ x ↑≡Γ ⟧≡Γ ≡ x
⟦⟧≡Γ-id {.ε} {ε} refl = refl
⟦⟧≡Γ-id {.(y , y')} {y , y'} refl = cong₂ (cong₂ _,_) (⟦⟧≡Γ-id {y} {y} refl) (⟦⟧≡τ-id {y'} {y'} refl)

≡Γ-eq-refl : {Γ : Con} → (x : Γ ≡Γ Γ) → x ≡ ≡Γrefl
≡Γ-eq-refl ε = refl
≡Γ-eq-refl (p1 , p2) = cong₂ _,_ (≡Γ-eq-refl p1) (≡τ-eq-refl p2)

≡Γ-eq-eq : {Γ Δ : Con} → (p1 p2 : Γ ≡Γ Δ) → p1 ≡ p2
≡Γ-eq-eq p1 p2 with ⟦ p1 ⟧≡Γ
... | refl = trans (≡Γ-eq-refl p1) (sym (≡Γ-eq-refl p2))

!_,_>∋_ : ∀ {Γ Δ τ σ} → Γ ≡Γ Δ → τ ≡τ σ → (y : Γ ∋ τ) → Δ ∋ σ
! ε , p2 >∋ ()
! (p1 , p3) , p2 >∋ vz with ⟦ ≡τtrans (≡τsym p3) p2 ⟧≡τ
! (p1 , p3) , p2 >∋ vz | refl = vz
! (p1 , p3) , p2 >∋ vs y = vs (! p1 , p2 >∋ y)

!_,_>⊢_ : ∀ {Γ Δ τ σ} → Γ ≡Γ Δ → τ ≡τ σ → (t : Γ ⊢ τ) → Δ ⊢ σ
! p1 , p2 >⊢ var y = var (! p1 , p2 >∋ y)
! p1 , p2 ⇒ p3 >⊢ Λ y = Λ (! (p1 , p2) , p3 >⊢ y)
! p1 , p2 >⊢ (y · y') = ! p1 , ≡τrefl ⇒ p2 >⊢ y · ! p1 , ≡τrefl >⊢ y'

!_,_>=>_ : ∀ {Γ Γ' Δ Δ'} → Γ ≡Γ Γ' → Δ ≡Γ Δ' → (Γ => Δ) → Γ' => Δ'
! ε , p2 >=> sz = sz
! (p1 , p3) , p2 >=> ss y y' = ss (! p1 , p2 >=> y) (! p2 , p3 >⊢ y')

!,∋-id : ∀ {Γ τ} → (p : Γ ≡Γ Γ) → (p' : τ ≡τ τ) → (y : Γ ∋ τ) → ! p , p' >∋ y ≡ y
!,∋-id ε p' ()
!,∋-id (p1 , p2) p' vz with ⟦ ≡τtrans (≡τsym p2) p' ⟧≡τ
... | refl = refl
!,∋-id (p1 , p2) p' (vs y) = cong vs (!,∋-id p1 p' y)

!,⊢-id : ∀ {Γ τ} → (p : Γ ≡Γ Γ) → (p' : τ ≡τ τ) → (t : Γ ⊢ τ) 
        → ! p , p' >⊢ t ≡ t
!,⊢-id p p' (var y) = cong var (!,∋-id p p' y)
!,⊢-id p (p1 ⇒ p2) (Λ y) = cong Λ (!,⊢-id (p , p1) p2 y)
!,⊢-id p p' (y · y') = cong₂ _·_ (!,⊢-id p (≡τrefl ⇒ p') y) (!,⊢-id p ≡τrefl y')

!,=>-id : ∀ {Γ Δ} → (p : Γ ≡Γ Γ) → (p' : Δ ≡Γ Δ) → (s : Γ => Δ)
        → ! p , p' >=> s ≡ s
!,=>-id ε p' sz = refl
!,=>-id (p1 , p2) p' (ss y y') = cong₂ ss (!,=>-id p1 p' y) (!,⊢-id p' p2 y')

import Relation.Binary.EqReasoning

cong-!>⊢ : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (t t2 : Γ ⊢ τ) → t βη-≡ t2
         → (! p1 , p2 >⊢ t) βη-≡ (! p1 , p2 >⊢ t2)
cong-!>⊢ p1 p t t2 eq with ⟦ p1 ⟧≡Γ | ⟦ p ⟧≡τ
... | refl | refl =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %≡ !,⊢-id p1 p t ⟩
     _ ⟷⟨ eq ⟩
     _ ⟷⟨ bsym (%≡ !,⊢-id p1 p t2) ⟩
     _ ∎

!,∋vz : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p p' : τ ≡τ σ) → ! (p1 , p) , p' >∋ vz ≡ vz 
!,∋vz p1 p p' with ⟦ ≡τtrans (≡τsym p) p' ⟧≡τ
... | refl = refl

!,∋vz-flip : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p : τ ≡τ σ) → ! (p1 , ≡τrefl) , p >∋ vz ≡ ! (p1 , ≡τsym p) , ≡τrefl >∋ vz 
!,∋vz-flip p1 p with ⟦ p ⟧≡τ
!,∋vz-flip p1 p | refl with ≡τ-eq-refl p
!,∋vz-flip p1 .≡τrefl | refl | refl = cong (λ v → ! (p1 , v) , ≡τrefl >∋ vz) (≡τ-eq-eq _ _)

-≡Γ : ∀ {Γ Δ τ σ} → (p : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (v : Γ ∋ τ) 
      → Γ - v ≡Γ Δ - (! p , p2 >∋ v)
-≡Γ ε p2 ()
-≡Γ (p1 , p2) p vz with ⟦ ≡τtrans (≡τsym p2) p ⟧≡τ
-≡Γ (p1 , p2) p vz | refl = p1
-≡Γ (p1 , p2) p (vs y) with ⟦ p2 ⟧≡τ
... | refl = (-≡Γ p1 p y) , ≡τrefl

-≡Γvz : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (-≡Γ (p1 , p2) p2 vz) ≡ (≡subst (\v → Γ ≡Γ (Δ , σ - v)) (sym (!,∋vz p1 p2 p2)) p1) 
-≡Γvz p p2 with ⟦ ≡τtrans (≡τsym p2) p2 ⟧≡τ
... | refl = refl

-≡Γvs : ∀ {Γ Δ σ σ' τ τ'} → (p : Γ ≡Γ Δ) → (p2 : τ ≡τ τ') → (p3 : σ ≡τ σ')
      → (v : Γ ∋ σ) → (-≡Γ (p , p2) p3 (vs v)) ≡ ((-≡Γ p p3 v) , p2)
-≡Γvs p p2 p3 v with ⟦ p2 ⟧≡τ
... | refl = cong (_,_ (-≡Γ p p3 v)) (sym (≡τ-eq-refl p2))

!,⊢wkv : ∀ {Γ Δ τ σ a b} → (v : Γ ∋ a) → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) 
       → (p3 : a ≡τ b) → (y : Γ - v ∋ τ) 
       → ! p1 , p2 >∋ wkv v y 
       ≡ wkv (! p1 , p3 >∋ v) (! (-≡Γ p1 p3 v) , p2 >∋ y)
!,⊢wkv vz (p1 , p2) p3 p y with  ⟦ ≡τtrans (≡τsym p2) p ⟧≡τ
!,⊢wkv vz (p1 , p2) p3 p y | refl = refl
!,⊢wkv (vs y) (p1 , p2) p3 p vz with ⟦ p2 ⟧≡τ |  ⟦ ≡τtrans (≡τsym p2) p3 ⟧≡τ
!,⊢wkv (vs y) (p1 , p2) p3 p vz | refl | refl with ⟦ ≡τtrans (≡τsym ≡τrefl) p3 ⟧≡τ
... | refl = refl
!,⊢wkv (vs y) (p1 , p2) p3 p (vs y') with ⟦ p2 ⟧≡τ
!,⊢wkv (vs y) (p1 , p2) p3 p (vs y') | refl = cong vs (!,⊢wkv y p1 p3 p y')

open ≡-Reasoning

!,⊢wkTm : ∀ {Γ Δ τ σ a b} → (v : Γ ∋ a) → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) 
        → (p3 : a ≡τ b) → (t : Γ - v ⊢ τ) 
        → ! p1 , p2 >⊢ wkTm v t 
        ≡ wkTm (! p1 , p3 >∋ v) (! (-≡Γ p1 p3 v) , p2 >⊢ t)
!,⊢wkTm v p1 p2 p3 (var y) = cong var (!,⊢wkv v p1 p2 p3 y)
!,⊢wkTm v p1 (p2 ⇒ p3) p (Λ y) =
   begin
   _ ≡⟨ cong Λ (!,⊢wkTm (vs v) (p1 , p2) p3 p y) ⟩
   _ ≡⟨ cong (λ v' → Λ (wkTm (vs (! p1 , p >∋ v)) (! v' , p3 >⊢ y)))
          (-≡Γvs p1 p2 p v) ⟩
   _ ∎
!,⊢wkTm v p1 p2 p (y · y') = cong₂ _·_ (!,⊢wkTm v p1 (≡τrefl ⇒ p2) p y) (!,⊢wkTm v p1 (≡τrefl) p y')

!,⊢wkTmvz : ∀ {Γ Δ τ σ a b} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (p3 : a ≡τ b)
          → (t : Γ ⊢ τ) 
          → ! (p1 , p3) , p2 >⊢ wkTm vz t ≡ wkTm vz (! p1 , p2 >⊢ t)
!,⊢wkTmvz {a = a} p1 p2 p3 t with !,⊢wkTm vz (p1 , p3) p2 p3 t
!,⊢wkTmvz {a = a} p1 p2 p3 t | r with ⟦ ≡τtrans (≡τsym p3) p3 ⟧≡τ
!,⊢wkTmvz p1 p2 p3 t | r | refl = r 

!,⊢up : ∀ {Γ Δ τ σ} → (p1 : Γ ≡Γ Δ) → (p2 : τ ≡τ σ) → (t : ε ⊢ τ) → (! p1 , p2 >⊢ (up t)) ≡ up (! ≡Γrefl , p2 >⊢ t)
!,⊢up ε p2 t = refl
!,⊢up {Δ , σ} (p1 , p2) p3 t with ⟦ p2 ⟧≡τ
!,⊢up {Δ , σ} (p1 , p2) p3 t | refl =
  begin
  _ ≡⟨ cong (λ v → ! (p1 , v) , p3 >⊢ wkTm vz (up t)) (≡τ-eq-refl p2) ⟩
  _ ≡⟨ !,⊢wkTmvz p1 p3 ≡τrefl (up t) ⟩
  _ ≡⟨ cong (wkTm vz) (!,⊢up p1 p3 t) ⟩
  _ ∎

!,⊢· : ∀ {Γ Δ τ τ' σ σ'} → (p1 : Γ ≡Γ Δ) → (p2 : τ' ≡τ τ) → (p3 : σ ≡τ σ')
    → (f : Γ ⊢ τ ⇒ σ) → (a : Γ ⊢ τ') 
    → (! p1 , ≡τrefl ⇒ p3 >⊢ f) · (! p1 , p2 >⊢ a) 
    ≡ (! p1 , ≡τsym p2 ⇒ p3 >⊢ f) · (! p1 , ≡τrefl >⊢ a)
!,⊢· p1 p2 p3 f a with ⟦ p2 ⟧≡τ
!,⊢· p1 p2 p3 f a | refl with ≡τ-eq-refl p2
!,⊢· p1 .≡τrefl p3 f a | refl | refl = cong (λ v → ! p1 , v ⇒ p3 >⊢ f · ! p1 , ≡τrefl >⊢ a) (sym (≡τ-eq-refl (≡τsym ≡τrefl)))

!,⊢/ : ∀ {Γ Γ' Δ Δ' τ} → (p1 : Γ ≡Γ Γ') → (p2 : Δ ≡Γ Δ')
     → (s : Γ => Δ) → (t : Γ' ⊢ τ) 
     → t / (! p1 , p2 >=> s) ≡ ! p2 , ≡τrefl >⊢ ((! ≡Γsym p1 , ≡τrefl >⊢ t) / s)
!,⊢/ p1 p2 s t with ⟦ p1 ⟧≡Γ | ⟦ p2 ⟧≡Γ
!,⊢/ p1 p2 s t | refl | refl =
     begin
     _ ≡⟨ cong (_/_ t) (!,=>-id _ _ _) ⟩
     _ ≡⟨ cong (λ v → v / s) (sym (!,⊢-id (≡Γsym p1) ≡τrefl t)) ⟩
     _ ≡⟨ sym (!,⊢-id _ _ _) ⟩
     _ ∎

!,=>wkSvz : ∀ {Γ Γ' Δ Δ' τ σ} → (p1 : Γ ≡Γ Γ') → (p2 : Δ ≡Γ Δ') → (p3 : τ ≡τ σ)
          → (t : Γ => Δ) 
          → ! p1 , (p2 , p3) >=> wkS vz t ≡ wkS vz (! p1 , p2 >=> t)
!,=>wkSvz ε p2 p3 sz = refl
!,=>wkSvz (p1 , p3) p2 p (ss y y') = cong₂ ss (!,=>wkSvz p1 p2 p y) (!,⊢wkTmvz p2 p3 p y')

!,⊢-comm-trans : ∀ {Γ Γ' Γ'' τ τ' τ''} → (p1 : Γ ≡Γ Γ') → (p2 : Γ' ≡Γ Γ'')
                → (q1 : τ ≡τ τ') → (q2 : τ' ≡τ τ'') → (t : Γ ⊢ τ)
                → ! p2 , q2 >⊢ (! p1 , q1 >⊢ t) 
                ≡ ! ≡Γtrans p1 p2 , ≡τtrans q1 q2 >⊢ t
!,⊢-comm-trans p1 p2 q1 q2 t with ⟦ p1 ⟧≡Γ | ⟦ p2 ⟧≡Γ | ⟦ q1 ⟧≡τ | ⟦ q2 ⟧≡τ
!,⊢-comm-trans p1 p2 q1 q2 t | refl | refl | refl | refl =
  begin
  _ ≡⟨ !,⊢-id _ _ _ ⟩
  _ ≡⟨ !,⊢-id _ _ _ ⟩
  _ ≡⟨ sym (!,⊢-id _ _ _) ⟩
  _ ∎

!>=>-mod-proof : ∀ {Γ Γ' Δ Δ'} → (p1 p2 : Γ ≡Γ Γ') → (q1 q2 : Δ ≡Γ Δ') 
               → (s : Γ => Δ) → ! p1 , q1 >=> s ≡ ! p2 , q2 >=> s
!>=>-mod-proof p1 p2 q1 q2 s with ⟦ p1 ⟧≡Γ | ⟦ q1 ⟧≡Γ
... | refl | refl = cong₂ (λ v v' → ! v , v' >=> s) (≡Γ-eq-eq p1 p2) (≡Γ-eq-eq q1 q2)

\end{code}
