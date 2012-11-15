\begin{code}

module STLC.Term.Operations.Close where

open import STLC.Term.Base             
open import STLC.Term.Congruence
open import STLC.Term.Convertibility             
open import STLC.Term.Operations.Simultaneous
open import STLC.Term.Operations.Weaken
open import Util.PropositionalEquality

open ≡-Reasoning

infix 3 _↓

data _↓ : (Γ : Con) → Set where
  ε    : ε ↓
  cls  : ∀ {τ Γ} → Γ ↓ → Γ ⊢ τ → Γ , τ ↓

↓-=> : ∀ {Γ} → Γ ↓ → Γ => ε
↓-=> ε          = sz
↓-=> (cls y y') = ss (↓-=> y) (y' / ↓-=> y)

close : ∀ {Γ τ} → Γ ⊢ τ → Γ ↓ → ε ⊢ τ
close t s = t / ↓-=> s

%close : ∀ {Γ τ} {e e' : Γ ⊢ τ} → (s : Γ ↓) → e βη-≡ e' 
       → close e s βη-≡ close e' s
%close ε eq = eq %/- sz 
%close (cls y y') eq = eq %/- ss (↓-=> y) (y' / ↓-=> y)

open import Relation.Binary hiding (_⇒_)

!_>↓_ : ∀ {Γ Δ} → Γ ≡Γ Δ → Γ ↓ → Δ ↓
! ε >↓ ε = ε
! p1 , p2 >↓ cls y y' = cls (! p1 >↓ y) (! p1 , p2 >⊢ y')

!,=>-↓-=> : ∀ {Γ Δ} → (p : Γ ≡Γ Δ) → (s : Γ ↓) 
          → ! p , ε >=> ↓-=> s ≡ ↓-=> (! p >↓ s)
!,=>-↓-=> ε ε = refl
!,=>-↓-=> (p1 , p2) (cls y y') = ≡ss (!,=>-↓-=> p1 y) (trans (!,=>-/ p1 ε p2 y' _) (■' (! p1 , p2 >⊢ y') ≡/ !,=>-↓-=> p1 y))

!,⊢-close : ∀ {Γ Δ τ τ'} → (p : Γ ≡Γ Δ) → (p' : τ ≡τ τ') → (e : Γ ⊢ τ) → (s : Γ ↓)
          → ! ε , p' >⊢ close e s ≡ close (! p , p' >⊢ e) (! p >↓ s)
!,⊢-close p p' e s = 
 begin
 _ ≡⟨ !,=>-/ p ε p' e (↓-=> s) ⟩
 _ ≡⟨ ■' (! p , p' >⊢ e) ≡/ !,=>-↓-=> p s ⟩
 _ ∎
{-
infix 1 _βη↓_

data _βη↓_ : {Γ : Con} → Γ ↓ → Δ ⊂ Γ → Set where
  ε : ∀ {Δ} → (ε {Δ}) βη⊂ ε
  cls : ∀ {τ Δ Γ} {s1 s2 : Δ ⊂ Γ} {t1 t2 : Γ ⊢ τ} 
      → s1 βη⊂ s2 → t1 βη-≡ t2 → cls s1 t1 βη⊂ cls s2 t2

⊂refl : ∀ {Γ Δ} {s : Δ ⊂ Γ} → s βη⊂ s
⊂refl {s = ε} = ε
⊂refl {s = cls y y'} = cls ⊂refl □

⊂sym : ∀ {Γ Δ} {s s' : Δ ⊂ Γ} → s βη⊂ s' → s' βη⊂ s
⊂sym ε = ε
⊂sym (cls y y') = cls (⊂sym y) (bsym y')

⊂trans : ∀ {Γ Δ} {s s' s'' : Δ ⊂ Γ} → s βη⊂ s' → s' βη⊂ s'' → s βη⊂ s''
⊂trans ε v2 = v2
⊂trans (cls y y') (cls y0 y1) = cls (⊂trans y y0) (y' ⟷ y1)

βη⊂setoid : {Δ Γ : Con} → Setoid _ _
βη⊂setoid {Δ} {Γ} = 
  record { Carrier = Δ ⊂ Γ
         ; _≈_ = _βη⊂_
         ; isEquivalence = 
                         record { refl  = ⊂refl
                                ; sym   = ⊂sym
                                ; trans = ⊂trans
                         }                              
         }

  


-}
\end{code}