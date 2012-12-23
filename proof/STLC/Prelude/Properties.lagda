%if False
\begin{code}
module STLC.Prelude.Properties where

open import STLC.Term
open import STLC.Prelude.Base

import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

eval-comp : ∀ {a b c Γ} → (f2 : Γ ⊢ b ⇒ c) → (f1 : Γ ⊢ a ⇒ b) → f2 ∘ f1 βη-≡ Λ (weaken f2 · (weaken f1 · var vz))
eval-comp f2 f1 =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ beta %· □ ⟩
     _ ⟷⟨ beta ⟩
     _ ⟷⟨ %Λ (%≡ wk-ext/ vz (wkTm vz f2) _ _ 
          ⟷ (%≡ wk-ext/ vz f2 _ _ 
          ⟷ %≡ wk/ vz f2 I
          ⟷ %wkTm vz (%≡ /I f2)) %· □)
         ⟩
     _ ∎

do-comp : ∀ {a b c Γ} → (f2 : Γ ⊢ b ⇒ c) → (f1 : Γ ⊢ a ⇒ b) → (a : Γ ⊢ a) → ((f2 ∘ f1) · a) βη-≡ (f2 · (f1 · a))
do-comp f2 f1 a = 
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
    in begin
    _ ⟷⟨ eval-comp _ _ %· □ ⟩
    _ ⟷⟨ beta ⟩
    _ ⟷⟨ %≡ wk-ext/ vz f2 _ _ ⟷ %≡ /I f2 
      %· (%≡ wk-ext/ vz f1 _ _ ⟷ %≡ /I f1 %· □) ⟩
    _ ∎

infixl 2 _%∘_

_%∘_ : ∀ {Γ a b c} → {f₁ f₁' : Γ ⊢ (a ⇒ b)} → {f₂ f₂' : Γ ⊢ (b ⇒ c)} → f₂ βη-≡ f₂' → f₁ βη-≡ f₁' → f₂ ∘ f₁ βη-≡ f₂' ∘ f₁'
_%∘_ p1 p2 = □ %· p1 %· p2

\end{code}
%endif

\begin{code}
comp-assoc  : ∀ {a b c d Γ} → (f3 : Γ ⊢ c ⇒ d) → (f2 : Γ ⊢ b ⇒ c) 
            → (f1 : Γ ⊢ a ⇒ b) → f3 ∘ (f2 ∘ f1) βη-≡ (f3 ∘ f2) ∘ f1
comp-assoc f3 f2 f1 =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ (do-comp _ _ _ ⟷ (□ %· do-comp _ _ _)) ⟩
     _ ⟷⟨ %Λ (bsym (do-comp _ _ _) ⟷ bsym (do-comp _ _ _)) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎
\end{code}

%if False
\begin{code}
id-id : ∀ {Γ τ} → (t : Γ ⊢ τ) → id · t βη-≡ t
id-id t = beta

id-comp : ∀ {Γ a b} → (f : Γ ⊢ a ⇒ b) → id ∘ f βη-≡ f
id-comp f =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ do-comp _ _ _ ⟩
     _ ⟷⟨ %Λ beta ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

comp-id : ∀ {Γ a b} → (f : Γ ⊢ a ⇒ b) → f ∘ id βη-≡ f
comp-id f =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in begin
     _ ⟷⟨ bsym eta ⟩
     _ ⟷⟨ %Λ do-comp _ _ _ ⟩
     _ ⟷⟨ %Λ (□ %· beta) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎

\end{code}
%endif