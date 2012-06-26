\begin{code}
module STLC.Prelude where

open import STLC.Base
open import STLC.Eval
open import STLC.Syntax

import Relation.Binary.EqReasoning

idε : ∀ {a} → ε ⊢ a ⇒ a
idε = Λ (var vz)

id : ∀ {a Γ} → Γ ⊢ a ⇒ a
id = up idε

comp : ∀ {a b c} → ε ⊢ (b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
comp = Λ (Λ (Λ (var (vs (vs vz)) · (var (vs vz) · var vz))))

infixl 2 _∘_
_∘_ : ∀ {a b c Γ} → Γ ⊢ (b ⇒ c) → Γ ⊢ (a ⇒ b) → Γ ⊢ (a ⇒ c)
t1 ∘ t2 = up comp · t1 · t2

do-comp : ∀ {a b c Γ} → (f2 : Γ ⊢ b ⇒ c) → (f1 : Γ ⊢ a ⇒ b) → (a : Γ ⊢ a) → ((f2 ∘ f1) · a) βη-≡ (f2 · (f1 · a))
do-comp f2 f1 a = 
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
    in begin
    _ ⟷⟨ ((%≡ up-/sz _ %· □) ⟷ beta) %· □ %· □ ⟩
    _ ⟷⟨ beta ⟷ %Λ (%≡ wk-ext/ vz (wkTm vz f2) _ _ ⟷ (%≡ wk-ext/ vz f2 _ _ ⟷ %≡ wkS-ι vz f2) %· □) %· □ ⟩
    _ ⟷⟨ beta ⟷ ((%≡ wk-ext/ vz f2 _ _ ⟷ %≡ ι/ f2) %· (%≡ wk-ext/ vz f1 _ _ ⟷ %≡ ι/ f1 %· □)) ⟩
    _ ∎

infixl 2 _%∘_

_%∘_ : forall {Γ a b c} → {f₁ f₁' : Tm Γ (a ⇒ b)} → {f₂ f₂' : Tm Γ (b ⇒ c)} → f₂ βη-≡ f₂' → f₁ βη-≡ f₁' → f₂ ∘ f₁ βη-≡ f₂' ∘ f₁'
_%∘_ p1 p2 = □ %· p1 %· p2

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

up-comp : ∀ {a b c Γ} → (f2 : ε ⊢ b ⇒ c) → (f1 : ε ⊢ a ⇒ b) → up f2 ∘ up f1 βη-≡ up {Γ} (f2 ∘ f1)
up-comp f2 f1 =
   let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ %≡ up-/sz _ %· %≡ up-/sz _ %· %≡ up-/sz _ ⟩
     _ ⟷⟨ bsym (%≡ up-/sz _) ⟩
     _ ∎

id-comp : ∀ {a b} → (f : ε ⊢ a ⇒ b) → idε ∘ f βη-≡ f
id-comp f =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ β≡ (%Λ β≡ eta) %· □ ⟩
       id · f
     ⟷⟨ β≡ brefl ⟩
     _ ∎

\end{code}