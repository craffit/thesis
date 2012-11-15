\begin{code}

module STLC.Term.Congruence where

open import STLC.Term.Base
open import STLC.Variable.Congruence
open import STLC.Context.Equality
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infix 11 !_,_>⊢_
infix 11 ≡!_,_>⊢_

!_,_>⊢_ : ∀ {Γ Δ τ σ} → Γ ≡Γ Δ → τ ≡τ σ → (t : Γ ⊢ τ) → Δ ⊢ σ
! p1 , p2 >⊢ var y = var (! p1 , p2 >∋ y)
! p1 , p2 ⇒ p3 >⊢ Λ y = Λ (! (p1 , p2) , p3 >⊢ y)
! p1 , p2 >⊢ (y · y') = ! p1 , ≡τrefl ⇒ p2 >⊢ y · ! p1 , ≡τrefl >⊢ y'

≡!_,_>⊢_ : ∀ {Γ Δ τ σ} → {g g' : Γ ≡Γ Δ} → {t t' : τ ≡τ σ} → {y y' : Γ ⊢ τ} →
         g ≡ g' → t ≡ t' → y ≡ y' → ! g , t >⊢ y ≡ ! g' , t' >⊢ y'
≡! refl , refl >⊢ refl = refl         

!,⊢-id : ∀ {Γ τ} → (p : Γ ≡Γ Γ) → (p' : τ ≡τ τ) → (t : Γ ⊢ τ) 
        → ! p , p' >⊢ t ≡ t
!,⊢-id p p' (var y) = ≡var (!,∋-id p p' y)
!,⊢-id p (p1 ⇒ p2) (Λ y) = ≡Λ (!,⊢-id (p , p1) p2 y)
!,⊢-id p p' (y · y') = !,⊢-id p (≡τrefl ⇒ p') y ≡· !,⊢-id p ≡τrefl y'

!,⊢-mod-proof : ∀ {Γ Γ' τ τ'} → (p1 p2 : Γ ≡Γ Γ') → (q1 q2 : τ ≡τ τ') 
    → (s : Γ ⊢ τ) → ! p1 , q1 >⊢ s ≡ ! p2 , q2 >⊢ s
!,⊢-mod-proof p1 p2 q1 q2 s with ≡Γ-≡ p1 | ≡τ-≡ q1
... | refl | refl = ≡! ≡Γ-eq-eq p1 p2 , ≡τ-eq-eq q1 q2 >⊢ refl

!,⊢· : ∀ {Γ Δ τ τ' σ σ'} → (p1 : Γ ≡Γ Δ) → (p2 : τ' ≡τ τ) → (p3 : σ ≡τ σ')
    → (f : Γ ⊢ τ ⇒ σ) → (a : Γ ⊢ τ') 
    → (! p1 , ≡τrefl ⇒ p3 >⊢ f) · (! p1 , p2 >⊢ a) 
    ≡ (! p1 , ≡τsym p2 ⇒ p3 >⊢ f) · (! p1 , ≡τrefl >⊢ a)
!,⊢· p1 p2 p3 f a with ≡τ-≡ p2
!,⊢· p1 p2 p3 f a | refl with ≡τ-eq-refl p2
!,⊢· p1 .≡τrefl p3 f a | refl | refl = !,⊢-mod-proof p1 p1 (≡τrefl ⇒ p3) (≡τsym ≡τrefl ⇒ p3) f ≡· refl

!,⊢-comm-trans : ∀ {Γ Γ' Γ'' τ τ' τ''} → (p1 : Γ ≡Γ Γ') → (p2 : Γ' ≡Γ Γ'')
                → (q1 : τ ≡τ τ') → (q2 : τ' ≡τ τ'') → (t : Γ ⊢ τ)
                → ! p2 , q2 >⊢ (! p1 , q1 >⊢ t) 
                ≡ ! ≡Γtrans p1 p2 , ≡τtrans q1 q2 >⊢ t
!,⊢-comm-trans p1 p2 q1 q2 t with ≡Γ-≡ p1 | ≡Γ-≡ p2 | ≡τ-≡ q1 | ≡τ-≡ q2
!,⊢-comm-trans p1 p2 q1 q2 t | refl | refl | refl | refl =
  begin
  _ ≡⟨ !,⊢-id _ _ _ ⟩
  _ ≡⟨ !,⊢-id _ _ _ ⟩
  _ ≡⟨ sym (!,⊢-id _ _ _) ⟩
  _ ∎

!,⊢-split-· : ∀ {Γ Δ τ τ' σ σ'} → (f : Γ ⊢ σ ⇒ τ) → (a : Γ ⊢ σ)
              → (p1 : Γ ≡Γ Δ) → (p2 : σ ≡τ σ') → (p3 : τ ≡τ τ')
              → (! p1 , p2 ⇒ p3 >⊢ f) · (! p1 , p2 >⊢ a) ≡ ! p1 , p3 >⊢ (f · a)
!,⊢-split-· f a p1 p2 p3 with ≡Γ-≡ p1 | ≡τ-≡ p2 | ≡τ-≡ p3
... | refl | refl | refl =
    let open ≡-Reasoning
    in begin
       _ ≡⟨ !,⊢-id _ _ _ ≡· !,⊢-id _ _ _ ⟩
       _ ≡⟨ sym (!,⊢-id _ _ _) ⟩
       _ ∎
  
\end{code}