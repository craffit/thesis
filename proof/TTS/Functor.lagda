%if False
\begin{code}
module TTS.Functor where

open import STLC

import Relation.Binary.EqReasoning

infixr 4 _⟶_
\end{code}
%endif

With the object language laid out, we can now develop a representation for our TTS in Agda. Essential to the type and transform system is the typing functor. The typing functor is defined as a straightforward inductive family as follows:

\begin{code}
data Functor : Set where
  Id   : Functor
  K    : (τ : Ty) → Functor
  _⟶_  : (Φ₁ Φ₂ : Functor) → Functor
\end{code}

The |Id| constructor represents the hole in the functor and the |K| constructor represents a constant type from the object language. Function space is represented by |_⟶_|. The functor data type is essentially a universe type for functors. We can interpret this universe in as types in the object language, yielding the following interpretation function:

\begin{code} 
⟦_⟧Φ_ : Functor → Ty → Ty
⟦ Id       ⟧Φ τ = τ
⟦ K σ      ⟧Φ τ = σ     
⟦ Φ₁ ⟶ Φ₂  ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ
\end{code}

The functor interpretation function takes a functor and a type to fill into the hole element and constructs a type in our object language. Using this interpretation on the type level, we can also construct an accompanying term-level functor for the object language. 

\begin{code}
dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ (a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a
dimap Id         = Λ (Λ (v 0))
dimap (K τ)      = Λ (Λ (up idε))
dimap (Φ₁ ⟶ Φ₂)  = Λ (Λ (Λ (up (dimap Φ₂) · v 2 · v 1 ∘ v 0 ∘ up (dimap Φ₁) · v 1 · v 2)))
\end{code}

For the hole type, the covariant function parameter is ap
To show that we have constructed a proper functor, we can now give proof of the functor laws. The functor laws are formulated as follows:

%if False
\begin{code}

do-dimap : ∀ {Φ₁ Φ₂ a b} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) 
         → dimap (Φ₁ ⟶ Φ₂) · f1 · f2 βη-≡ Λ (up (dimap Φ₂ · f1 · f2) ∘ v 0 ∘ up (dimap Φ₁ · f2 · f1))
do-dimap {Φ₁} {Φ₂} f1 f2 =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta %· □ ⟩
--       _ ⟷⟨ %Λ (%Λ (□ %· !upw-up f1 %· □ %∘ □ %∘ □ %· □ %· !upw-up f1)) %· □ ⟩
       _ ⟷⟨ %Λ (%Λ (!up/ (dimap Φ₂) (ss (ss (ss sz (up f1)) (v 1)) (v 0)) %· □ %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss (ss sz (up f1)) (v 1)) (v 0)) %· □ %· □)) %· □ ⟩
       _ ⟷⟨ beta ⟩
--       _ ⟷⟨ %Λ (□ %· □ %· !upw-up f2 %∘ □ %∘ □ %· !upw-up f2 %· □) ⟩
       _ ⟷⟨ %Λ (!up/ (dimap Φ₂ · f1) (ss (ss sz (wkTm vz f2)) (v 0)) %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss sz (wkTm vz f2)) (v 0)) %· □ %· !up/ f1 (ss (ss sz (wkTm vz f2)) (v 0))) ⟩
       _ ∎

do-dimap' : ∀ {Φ₁ Φ₂ a b Γ} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) → (e : Γ ⊢ ⟦ Φ₁ ⟶ Φ₂ ⟧Φ b)
         → up (dimap (Φ₁ ⟶ Φ₂) · f1 · f2) · e βη-≡ up (dimap Φ₂ · f1 · f2) ∘ e ∘ up (dimap Φ₁ · f2 · f1)
do-dimap' {Φ₁} {Φ₂} f1 f2 e =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ %up do-dimap {Φ₁} {Φ₂} f1 f2 %· □ ⟩
       _ ⟷⟨ %≡ up-/sz _ %· □ ⟩
       _ ⟷⟨ %Λ (□ %· (□ %· %≡ wk-ext/ vz (dimap Φ₂ · f1 · f2) _ _ %· □) %· %≡ wk-ext/ vz (dimap Φ₁ · f2 · f1) _ _) %· □ ⟩
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ bsym (%≡ up-/sz _) %· (bsym (%≡ up-/sz _) %· □ %· □) %· □ ⟩
       _ ⟷⟨ %≡ comm-/-/=> (dimap Φ₂ · f1 · f2) _ _ %∘ □ %∘ %≡ comm-/-/=> (dimap Φ₁ · f2 · f1) _ _ ⟩
       _ ⟷⟨ bsym (%≡ up-/sz _) %∘ □ %∘ bsym (%≡ up-/sz _) ⟩
       _ ∎
\end{code}
%endif

\begin{code}
dimapid : ∀ {τ} → (Φ : Functor) → dimap {τ} {τ} Φ · id · id βη-≡ id
\end{code}

%if False
\begin{code}
dimapid Id = β≡ brefl 
dimapid (K τ) = β≡ brefl
dimapid {a} (Φ₁ ⟶ Φ₂) =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ do-dimap {Φ₁} {Φ₂} id id ⟩
       _ ⟷⟨ %Λ (%up dimapid Φ₂ %∘ □ %∘ %up dimapid Φ₁) ⟩
       _ ⟷⟨ β≡ (β≡ (β≡ (%Λ eta))) ⟩
       _ ∎

\end{code}
%endif

\begin{code}
dimapcomp : ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
                → (f1 : ε ⊢ τ₃ ⇒ τ₂) → (f2 : ε ⊢ τ₂ ⇒ τ₃) 
                → (g1 : ε ⊢ τ₂ ⇒ τ₁) →  (g2 : ε ⊢ τ₁ ⇒ τ₂) 
                →     dimap Φ · f1 · f2 ∘ dimap Φ · g1 · g2
                βη-≡  dimap Φ · (g1 ∘ f1) · (f2 ∘ g2)
\end{code}

%if False
\begin{code}
dimapcomp Id f1 f2 g1 g2 = β≡ brefl
dimapcomp (K τ) f1 f2 g1 g2 = β≡ (β≡ brefl)
dimapcomp (Φ₁ ⟶ Φ₂) f1 f2 g1 g2 =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ do-dimap {Φ₁} {Φ₂} f1 f2 %∘ do-dimap {Φ₁} {Φ₂} g1 g2 ⟩
       _ ⟷⟨ bsym eta ⟩
       _ ⟷⟨ %Λ do-comp _ _ _ ⟩
       _ ⟷⟨ %Λ beta ⟩
       _ ⟷⟨ %Λ (%≡ wk-ext/ (vs vz) (up (dimap Φ₂ · f1 · f2)) (v 0) (ss sz _) %∘ □ %∘ %≡ wk-ext/ (vs vz) (up (dimap Φ₁ · f2 · f1)) (v 0) (ss sz _)) ⟩
       _ ⟷⟨ %Λ (!up/ _ (ss sz _) %∘ beta %∘ !up/ _ (ss sz _)) ⟩
       _ ⟷⟨ %Λ (□ %∘ (%≡ wk-ext/ (vs vz) (up (dimap Φ₂ · g1 · g2)) (v 0) (ss sz _) %∘ □ %∘ %≡ wk-ext/ (vs vz) (up (dimap Φ₁ · g2 · g1)) (v 0) (ss sz _)) %∘ □) ⟩
       _ ⟷⟨ %Λ (□ %∘ (!up/ (dimap Φ₂ · g1 · g2) (ss sz _) %∘ □ %∘ !up/ (dimap Φ₁ · g2 · g1) (ss sz _)) %∘ □) ⟩
       _ ⟷⟨ %Λ (bsym (comp-assoc _ _ _) ⟷ ((□ %∘ bsym (comp-assoc _ _ _)) ⟷ comp-assoc _ _ _) ⟷ (comp-assoc _ _ _ %∘ □)) ⟩
       _ ⟷⟨ %Λ (%up dimapcomp Φ₂ f1 f2 g1 g2 %∘ □ %∘ %up dimapcomp Φ₁ g2 g1 f2 f1) ⟩
       _ ⟷⟨ bsym (do-dimap {Φ₁} {Φ₂} (g1 ∘ f1) (f2 ∘ g2)) ⟩
       _ ∎
\end{code}
%endif
