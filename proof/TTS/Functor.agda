module TTS.Functor where

open import STLC

import Relation.Binary.EqReasoning

infixr 4 _⟶_

data Functor : Set where
  Id   : Functor
  K    : (τ : Ty) → Functor
  _⟶_ : (Φ₁ Φ₂ : Functor) → Functor
 
⟦_⟧Φ_ : Functor → Ty → Ty
⟦ Id ⟧Φ       τ = τ
⟦ K σ ⟧Φ      τ = σ     
⟦ Φ₁ ⟶ Φ₂ ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ

dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ ((a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a)
dimap Id         = Λ (Λ (var vz))
dimap (K τ)      = Λ (Λ (up idε))
dimap (Φ₁ ⟶ Φ₂) = Λ (Λ (Λ (up (dimap Φ₂) · var (vs (vs vz)) · var (vs vz) ∘ var vz ∘ up (dimap Φ₁) · var (vs vz) · var (vs (vs vz)))))

do-dimap : ∀ {Φ₁ Φ₂ a b} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) 
         → dimap (Φ₁ ⟶ Φ₂) · f1 · f2 βη-≡ Λ (up (dimap Φ₂ · f1 · f2) ∘ var vz ∘ up (dimap Φ₁ · f2 · f1))
do-dimap {Φ₁} {Φ₂} f1 f2 =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta ⟷ %Λ (%Λ (!up/ (dimap Φ₂) (ss (ss (ss sz (up f1)) (var (vs vz))) (var vz)) %· □ %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss (ss sz (up f1)) (var (vs vz))) (var vz)) %· □ %· □)) %· □ ⟩
       _ ⟷⟨ beta ⟷ %Λ (!up/ (dimap Φ₂ · f1) (ss (ss sz (wkTm vz f2)) (var vz)) %· □ %∘ □ %∘ !up/ (dimap Φ₁) (ss (ss sz (wkTm vz f2)) (var vz)) %· □ %· !up/ f1 (ss (ss sz (wkTm vz f2)) (var vz))) ⟩
       _ ∎

do-dimap' : ∀ {Φ₁ Φ₂ a b Γ} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) → (e : Γ ⊢ ⟦ Φ₁ ⟶ Φ₂ ⟧Φ b)
         → up (dimap (Φ₁ ⟶ Φ₂) · f1 · f2) · e βη-≡ up (dimap Φ₂ · f1 · f2) ∘ e ∘ up (dimap Φ₁ · f2 · f1)
do-dimap' {Φ₁} {Φ₂} f1 f2 e =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ %up do-dimap {Φ₁} {Φ₂} f1 f2 %· □ ⟩
       _ ⟷⟨ %≡ up-/sz _ ⟷ %Λ (bsym (%≡ up-/sz comp) %· (bsym (%≡ up-/sz comp) %· %≡ wk-ext/ vz (dimap Φ₂ · f1 · f2) _ _ ⟷ bsym (%≡ up-/sz (dimap Φ₂ · f1 · f2)) %· □) %· %≡ wk-ext/ vz (dimap Φ₁ · f2 · f1) _ _ ⟷ bsym (%≡ up-/sz (dimap Φ₁ · f2 · f1))) %· □ ⟩
       _ ⟷⟨ beta ⟷ (%≡ wk-ext/ vz (up comp) e ι ⟷ %≡ ι/ (up comp) %· (%≡ wk-ext/ vz (up comp · up (dimap Φ₂ · f1 · f2)) e ι ⟷ %≡ ι/ (up comp · up (dimap Φ₂ · f1 · f2)) %· □) %· %≡ wk-ext/ vz (up (dimap Φ₁ · f2 · f1)) e ι ⟷ %≡ ι/ (up (dimap Φ₁ · f2 · f1))) ⟩
       _ ∎
-- up-dimap : ∀ {Φ₁ Φ₂ a b} → (f1 : ε ⊢ a ⇒ b) → (f2 : ε ⊢ b ⇒ a) 
--         →  βη-≡ Λ (up (dimap Φ₂ · f1 · f2) ∘ var vz ∘ up (dimap Φ₁ · f2 · f1))
dimapid : ∀ {τ} → (Φ : Functor) → (dimap {τ} {τ} Φ · id · id) βη-≡ id
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

dimapcomp : ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
                → (f1 : ε ⊢ (τ₃ ⇒ τ₂)) → (f2 : ε ⊢ (τ₂ ⇒ τ₃)) →  (g1 : ε ⊢ (τ₂ ⇒ τ₁)) →  (g2 : ε ⊢ (τ₁ ⇒ τ₂)) 
                → (dimap Φ · f1 · f2 ∘ dimap Φ · g1 · g2) βη-≡ (dimap Φ · (g1 ∘ f1) · (f2 ∘ g2))
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
       _ ⟷⟨ %Λ (%≡ wk-ext/ (vs vz) (up (dimap Φ₂ · f1 · f2)) (var vz) (ss sz _) ⟷ !up/ (dimap Φ₂ · f1 · f2) (ss sz _) %∘ □ %∘ %≡ wk-ext/ (vs vz) (up (dimap Φ₁ · f2 · f1)) (var vz) (ss sz _) ⟷ !up/ (dimap Φ₁ · f2 · f1) (ss sz _)) ⟩
       _ ⟷⟨ %Λ (□ %∘ beta ⟷ (%≡ wk-ext/ (vs vz) (up (dimap Φ₂ · g1 · g2)) (var vz) (ss sz _) ⟷ !up/ (dimap Φ₂ · g1 · g2) (ss sz _) %∘ □ %∘ %≡ wk-ext/ (vs vz) (up (dimap Φ₁ · g2 · g1)) (var vz) (ss sz _) ⟷ !up/ (dimap Φ₁ · g2 · g1) (ss sz _)) %∘ □) ⟩
       _ ⟷⟨ %Λ (bsym (comp-assoc _ _ _) ⟷ ((□ %∘ bsym (comp-assoc _ _ _)) ⟷ comp-assoc _ _ _) ⟷ (comp-assoc _ _ _ %∘ □)) ⟩
       _ ⟷⟨ %Λ (%up dimapcomp Φ₂ f1 f2 g1 g2 %∘ □ %∘ %up dimapcomp Φ₁ g2 g1 f2 f1) ⟩
       _ ⟷⟨ bsym (do-dimap {Φ₁} {Φ₂} (g1 ∘ f1) (f2 ∘ g2)) ⟩
       _ ∎
{-
  open import Data.Empty

  tyl-neq : ∀ {τ σ} → τ ≡ τ ⇒ σ → ⊥
  tyl-neq ()

  tyr-neq : ∀ {τ σ} → τ ≡ σ ⇒ τ → ⊥
  tyr-neq ()

  occurs-left : ∀ {Φ τ Φ₁} → ⟦ Φ ⟧Φ τ ≡ (⟦ Φ ⟧Φ τ ⇒ ⟦ Φ₁ ⟧Φ τ) → ⊥
  occurs-left = tyl-neq

  occurs-right : ∀ {Φ τ Φ₁} → ⟦ Φ ⟧Φ τ ≡ (⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ ⟧Φ τ) → ⊥
  occurs-right = tyr-neq

  inj⟦⟧ΦTy : ∀ {Φ τ σ} → ⟦ Φ ⟧Φ τ ≡ ⟦ Φ ⟧Φ σ → τ ≡ σ
  inj⟦⟧ΦTy {Id} v = v
  inj⟦⟧ΦTy {Φ₁ ⟶ Φ₂} v = inj⟦⟧ΦTy {Φ₁} (tyInj-left v)

  neq⟦⟧Φ : ∀ {Φ τ σ} → (τ ≡ σ → ⊥) → ⟦ Φ ⟧Φ τ ≡ ⟦ Φ ⟧Φ σ → ⊥
  neq⟦⟧Φ {Id} n v = n v
  neq⟦⟧Φ {Φ₁ ⟶ Φ₂} n v = neq⟦⟧Φ {Φ₁} n (tyInj-left v)

  open import STLC.TySize
  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Nullary


  <≠ : ∀ {n m} → n < m → n ≡ m → ⊥
  <≠ (s≤s {zero} {n} m≤n) = λ ()
  <≠ (s≤s {suc n} {zero} ())
  <≠ (s≤s {suc n} {suc n'} (s≤s m≤n)) = λ refl → <≠ (s≤s m≤n) (cong pred refl)

  τsize-<Φ : ∀ {Φ τ} → τsize τ ≤ τsize (⟦ Φ ⟧Φ τ)
  τsize-<Φ {Id}      = ≡-to-≤ refl
  τsize-<Φ {Φ₁ ⟶ Φ₂} {τ} = ≤-steps (τsize (⟦ Φ₁ ⟧Φ τ)) (τsize-<Φ {Φ₂})

  τsize-occ< : (Φ₁ Φ₂ : Functor) → (τ : Ty) → τsize τ < (τsize (⟦ Φ₁ ⟧Φ τ) + τsize (⟦ Φ₂ ⟧Φ τ))
  τsize-occ< f1 f2 t = ≤+ (τsize-1 {⟦ f1 ⟧Φ t}) (τsize-<Φ {f2} {t})

  τsize-occ : ∀ {Φ₁ Φ₂ τ} → τsize τ ≡ (τsize (⟦ Φ₁ ⟧Φ τ) + τsize (⟦ Φ₂ ⟧Φ τ)) → ⊥
  τsize-occ {Φ₁} {Φ₂} {τ} p = <≠ (τsize-occ< Φ₁ Φ₂ τ) p

  -- Injectivity of functor interpretation
  inj⟦⟧Φ : ∀ {Φ₁ Φ₂ τ} → ⟦ Φ₁ ⟧Φ τ ≡ ⟦ Φ₂ ⟧Φ τ → Φ₁ ≡ Φ₂
  inj⟦⟧Φ {Id} {Id} refl = refl
  inj⟦⟧Φ {Id} {Φ₁ ⟶ Φ₂} {τ} v with τs-neq (τsize-occ {Φ₁} {Φ₂} {τ}) v
  ... | ()
  inj⟦⟧Φ {Φ₁ ⟶ Φ₂} {Id} {τ} v with τs-neq (τsize-occ {Φ₁} {Φ₂} {τ}) (sym v)
  ... | ()
  inj⟦⟧Φ {Φ₁ ⟶ Φ₂} {Φ₁' ⟶ Φ₂'} v = cong₂ _⟶_ (inj⟦⟧Φ (tyInj-left v)) (inj⟦⟧Φ (tyInj-right v))
-}
--  dimapid : ∀ {τ Γ} → (Φ : Functor) → ⟦ dimap {τ} {τ} {Γ} Φ · id · id ⟧ ≡ ⟦ id ⟧
--  dimapid Id = refl
--  dimapid (Φ₁ ⟶ Φ₂) = {!!}
