\begin{code}

module TTS.Functor.Properties where

open import STLC
open import TTS.Functor.Base
import Relation.Binary.EqReasoning

dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ (a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a
dimap Id         = Λ (Λ (v 0))
dimap (K n)      = Λ (Λ id)
dimap (Φ₁ ⟶ Φ₂) = Λ (Λ (Λ (up (dimap Φ₂) · v 2 · v 1 ∘ v 0 ∘ up (dimap Φ₁) · v 1 · v 2)))


do-dimap : ∀ {Φ₁ Φ₂ a b} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) 
         → dimap (Φ₁ ⟶ Φ₂) · f1 · f2 βη-≡ Λ (up (dimap Φ₂ · f1 · f2) ∘ v 0 ∘ up (dimap Φ₁ · f2 · f1))
do-dimap {Φ₁} {Φ₂} f1 f2 =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta %· □ ⟩
       _ ⟷⟨ %Λ (%Λ (%≡ merge-/ (dimap Φ₂) sz _ %· □ %· □ %∘ □ %∘ 
                      %≡ merge-/ (dimap Φ₁) sz _ %· □ %· □)) %· □ ⟩
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ %Λ (%≡ merge-/ (dimap Φ₂) sz _ %· □ %· □ %∘ □ %∘
                  %≡ merge-/ (dimap Φ₁) sz _ %· □ %· □) ⟩
       _ ⟷⟨ {!!} ⟩
--       _ ⟷⟨ %Λ (%Λ (□ %· !upw-up f1 %· □ %∘ □ %∘ □ %· □ %· !upw-up f1)) %· □ ⟩
 --      _ ⟷⟨ %Λ (%Λ (!up/ (dimap Φ₂) (ss (ss (ss sz (up f1)) (v 1)) (v 0)) %· □ %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss (ss sz (up f1)) (v 1)) (v 0)) %· □ %· □)) %· □ ⟩
--       _ ⟷⟨ beta ⟩
--       _ ⟷⟨ %Λ (□ %· □ %· !upw-up f2 %∘ □ %∘ □ %· !upw-up f2 %· □) ⟩
--       _ ⟷⟨ %Λ (!up/ (dimap Φ₂ · f1) (ss (ss sz (wkTm vz f2)) (v 0)) %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss sz (wkTm vz f2)) (v 0)) %· □ %· !up/ f1 (ss (ss sz (wkTm vz f2)) (v 0))) ⟩
       _ ∎
{-
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
       _ ⟷⟨ %≡ comm-/-/=> (dimap Φ₂ · f1 · f2) _ _ %∘ □ %∘ %≡ comm-/-/=> (dimap Φ₁ · f2 · f1) _ _ ⟩
       _ ⟷⟨ bsym (%≡ up-/sz _) %∘ □ %∘ bsym (%≡ up-/sz _) ⟩
       _ ∎


dimapid : ∀ {τ} → (Φ : Functor) → dimap {τ} {τ} Φ · id · id βη-≡ id
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

dimapcomp :  ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
             → (f1 : ε ⊢ τ₃ ⇒ τ₂) → (f2 : ε ⊢ τ₂ ⇒ τ₃) 
             → (g1 : ε ⊢ τ₂ ⇒ τ₁) → (g2 : ε ⊢ τ₁ ⇒ τ₂) 
             →     dimap Φ · f1 · f2 ∘ dimap Φ · g1 · g2
             βη-≡  dimap Φ · (g1 ∘ f1) · (f2 ∘ g2)

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
-}
\end{code}