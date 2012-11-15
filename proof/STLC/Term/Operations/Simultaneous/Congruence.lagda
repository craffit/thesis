\begin{code}

module STLC.Term.Operations.Simultaneous.Congruence where

open import STLC.Term.Base
open import STLC.Term.Operations.Weaken
open import STLC.Term.Operations.Simultaneous.Base
open import STLC.Term.Congruence
open import STLC.Context

open import Util.PropositionalEquality
open ≡-Reasoning

infix 11 !_,_>=>_

!_,_>=>_ : ∀ {Γ Γ' Δ Δ'} → Γ ≡Γ Γ' → Δ ≡Γ Δ' → Γ => Δ → Γ' => Δ'
! ε , p2 >=> sz = sz
! (p1 , p3) , p2 >=> ss y y' = ss (! p1 , p2 >=> y) (! p2 , p3 >⊢ y') 

!,=>-id : ∀ {Γ Δ} → (p1 : Γ ≡Γ Γ) → (p2 : Δ ≡Γ Δ) → (s : Γ => Δ)
        → ! p1 , p2 >=> s ≡ s
!,=>-id ε p2 sz = refl
!,=>-id (p1 , p3) p2 (ss y y') = ≡ss (!,=>-id p1 p2 y) (!,⊢-id p2 p3 y')


!,=>-wkSvz : ∀ {Γ Γ' Δ Δ' τ τ'} → (p : Γ ≡Γ Γ') → (p' : Δ ≡Γ Δ') → (p'' : τ ≡τ τ')
       → (s : Γ => Δ) → ! p , (p' , p'') >=> wkS vz s ≡ wkS vz (! p , p' >=> s) 
!,=>-wkSvz ε p' p'' sz = refl
!,=>-wkSvz (p1 , p2) p' p'' (ss y y') = ≡ss (!,=>-wkSvz p1 p' p'' y) (!,⊢wkTmvz p' p2 p'' y')

!,=>-lookup :  ∀ {Γ Γ' Δ Δ' τ τ'} → (p : Γ ≡Γ Γ') → (p' : Δ ≡Γ Δ') → (p'' : τ ≡τ τ')
       → (v : Γ ∋ τ) → (s : Γ => Δ) → ! p' , p'' >⊢ lookup v s 
       ≡ lookup (! p , p'' >∋ v) (! p , p' >=> s)
!,=>-lookup ε p' p'' () s
!,=>-lookup (p1 , p2) p' p'' vz (ss y y') with ≡τ-≡ (≡τtrans (≡τsym p2) p'')
... | refl = !,⊢-mod-proof p' p' p'' p2 y'
!,=>-lookup (p1 , p2) p' p'' (vs y) (ss y' y0) = !,=>-lookup p1 p' p'' y y'

!,=>-/ :  ∀ {Γ Γ' Δ Δ' τ τ'} → (p : Γ ≡Γ Γ') → (p' : Δ ≡Γ Δ') → (p'' : τ ≡τ τ')
       → (e : Γ ⊢ τ) → (s : Γ => Δ) → ! p' , p'' >⊢ (e / s) 
       ≡ ! p , p'' >⊢ e / ! p , p' >=> s
!,=>-/ p p' p'' (var y) s = !,=>-lookup p p' p'' y s
!,=>-/ p p' (p1 ⇒ p2) (Λ y) s =
 begin
 _ ≡⟨ ≡Λ (!,=>-/ (p , p1) (p' , p1) p2 y (wkExtS vz vz s)) ⟩
 _ ≡⟨ ≡Λ (≡! ■' (p , p1) , ■' p2 >⊢ (■' y) ≡/ ≡ss (!,=>-wkSvz p p' p1 s) (≡var (!,∋vz p' p1 p1))) ⟩
 _ ∎
!,=>-/ p p' p'' (y · y') s = !,=>-/ p p' (≡τrefl ⇒ p'') y s ≡· !,=>-/ p p' ≡τrefl y' s

\end{code}