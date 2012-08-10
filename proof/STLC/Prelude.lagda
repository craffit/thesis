%if False
\begin{code}
module STLC.Prelude where

open import STLC.Base
open import STLC.Equality
open import STLC.Syntax
open import STLC.Up
open import STLC.SSubst
open import STLC.Eval
open import STLC.Variables

import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality

idε : ∀ {a} → ε ⊢ a ⇒ a
idε = Λ (var vz)
\end{code}
%endif

These term construction tricks allow for reasonably convenient construction of terms in the object language, such as the basic identity, constant and composition functions:

\begin{code}

id : ∀ {a Γ} → Γ ⊢ a ⇒ a
id = Λ (v 0)

const : ∀ {a b Γ} → Γ ⊢ a ⇒ b ⇒ a
const = Λ (Λ (v 1))

infixl 2 _∘_
_∘_ : ∀ {a b c Γ} → Γ ⊢ b ⇒ c → Γ ⊢ a ⇒ b → Γ ⊢ a ⇒ c
t1 ∘ t2 = Λ (Λ (Λ (v 2 · (v 1 · v 0)))) · t1 · t2

\end{code}

%if False
\begin{code}
const' : ∀ {a b Γ} → Γ ⊢ b ⇒ a ⇒ a
const' = up (Λ (Λ (v 0)))

flip : ∀ {a b c Γ} → Γ ⊢ (a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c
flip = up (Λ (Λ (Λ (v 2 · v 0 · v 1))))

comp : ∀ {a b c} → ε ⊢ (b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
comp = Λ (Λ (Λ (v 2 · (v 1 · v 0))))

do-comp : ∀ {a b c Γ} → (f2 : Γ ⊢ b ⇒ c) → (f1 : Γ ⊢ a ⇒ b) → (a : Γ ⊢ a) → ((f2 ∘ f1) · a) βη-≡ (f2 · (f1 · a))
do-comp f2 f1 a = 
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
    in begin
    _ ⟷⟨ ((%≡ up-/sz _ %· □) ⟷ beta) %· □ %· □ ⟩
    _ ⟷⟨ beta ⟷ %Λ (%≡ wk-ext/ vz (wkTm vz f2) _ _ ⟷ (%≡ wk-ext/ vz f2 _ _ ⟷ %≡ wkS-ι vz f2) %· □) %· □ ⟩
    _ ⟷⟨ beta ⟷ ((%≡ wk-ext/ vz f2 _ _ ⟷ %≡ /ι f2) %· (%≡ wk-ext/ vz f1 _ _ ⟷ %≡ /ι f1 %· □)) ⟩
    _ ∎

infixl 2 _%∘_

_%∘_ : ∀ {Γ a b c} → {f₁ f₁' : Γ ⊢ (a ⇒ b)} → {f₂ f₂' : Γ ⊢ (b ⇒ c)} → f₂ βη-≡ f₂' → f₁ βη-≡ f₁' → f₂ ∘ f₁ βη-≡ f₂' ∘ f₁'
_%∘_ p1 p2 = □ %· p1 %· p2

!τ∘ : ∀ {Γ a a' b b' c c'} → (p1 : a ⇒ b ≡ a' ⇒ b') → (p2 : b ⇒ c ≡ b' ⇒ c')
   → (t1 : Γ ⊢ a ⇒ b) → (t2 : Γ ⊢ b ⇒ c)
   → (! p2 >τ t2 ∘ ! p1 >τ t1) ≡ ! cong₂ _⇒_ (tyInj-left p1) (tyInj-right p2) >τ (t2 ∘ t1)
!τ∘ refl refl t1 t2 = refl

comp-assoc : ∀ {a b c d Γ} → (f3 : Γ ⊢ c ⇒ d) → (f2 : Γ ⊢ b ⇒ c) → (f1 : Γ ⊢ a ⇒ b) → f3 ∘ (f2 ∘ f1) βη-≡ (f3 ∘ f2) ∘ f1
comp-assoc f3 f2 f1 =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ (do-comp _ _ _ ⟷ (□ %· do-comp _ _ _)) ⟩
     _ ⟷⟨ %Λ (bsym (do-comp _ _ _) ⟷ bsym (do-comp _ _ _)) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

id-id : ∀ {Γ τ} → (t : Γ ⊢ τ) → id · t βη-≡ t
id-id t = (%≡ up-/sz _ %· □) ⟷ beta

up-comp : ∀ {a b c Γ} → (f2 : ε ⊢ b ⇒ c) → (f1 : ε ⊢ a ⇒ b) → up f2 ∘ up f1 βη-≡ up {Γ} (f2 ∘ f1)
up-comp f2 f1 =
   let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ %≡ up-/sz _ %· %≡ up-/sz _ %· %≡ up-/sz _ ⟩
     _ ⟷⟨ bsym (%≡ up-/sz _) ⟩
     _ ∎

id-comp : ∀ {Γ a b} → (f : Γ ⊢ a ⇒ b) → id ∘ f βη-≡ f
id-comp f =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ do-comp _ _ _ ⟩
     _ ⟷⟨ %Λ id-id _ ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

comp-id : ∀ {Γ a b} → (f : Γ ⊢ a ⇒ b) → f ∘ id βη-≡ f
comp-id f =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ do-comp _ _ _ ⟩
     _ ⟷⟨ %Λ (□ %· id-id _) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

\end{code}
%endif