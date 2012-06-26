{-# OPTIONS --universe-polymorphism #-}
module TTS2 where

open import STLC.Core3

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
import Relation.Binary.EqReasoning

idε : ∀ {a} → ε ⊢ a ⇒ a
idε = Λ (var vz)

id : ∀ {a Γ} → Γ ⊢ a ⇒ a
id = Λ (var vz)

comp : ∀ {a b c Γ} → Γ ⊢ ((b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
comp = Λ (Λ (Λ (var (vs (vs vz)) · (var (vs vz) · var vz))))

infixl 2 _∘_
_∘_ : ∀ {a b c Γ} → Γ ⊢ b ⇒ c → Γ ⊢ a ⇒ b → Γ ⊢ a ⇒ c
t1 ∘ t2 = comp · t1 · t2

module Functor where

  infixr 4 _⟶_

  data Functor : Set where
    Id   : Functor
    _⟶_ : (Φ₁ Φ₂ : Functor) → Functor

  ⟦_⟧Φ_ : Functor → Ty → Ty
  ⟦ Id ⟧Φ       τ = τ
  ⟦ Φ₁ ⟶ Φ₂ ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ

  dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ (a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a
  dimap Id         = Λ (Λ (var vz))
  dimap (Φ₁ ⟶ Φ₂) = Λ (Λ (Λ (comb (dimap Φ₂) · var (vs (vs vz)) · var (vs vz) ∘ var vz ∘ comb (dimap Φ₁) · var (vs vz) · var (vs (vs vz)))))


  dimapid : ∀ {τ} → (Φ : Functor) →  ⟦ dimap {τ} {τ} Φ · id · id ⟧ ≡ ⟦ id ⟧
  dimapid Id = refl
  dimapid (Φ₁ ⟶ Φ₂) =
    let open ≡-Reasoning
    in begin
         ⟦ dimap (Φ₁ ⟶ Φ₂) · id · id ⟧
       ≡⟨ refl ⟩
         {!!}
       ≡⟨ {!!} ⟩
         ⟦ id ⟧
       ∎
{-
  dimapid : ∀ {τ} → (Φ : Functor) → (dimap {τ} {τ} Φ · idε · idε) βη-≡ idε 
  dimapid Id = 
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin 
         dimap Id · id · id
       ⟷⟨ congApp beta brefl ⟩
         id · id
       ⟷⟨ beta ⟩
         id
       ∎
     
  dimapid {a} (Φ₁ ⟶ Φ₂) =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin 
         dimap (Φ₁ ⟶ Φ₂) · id · id
       ⟷⟨ congApp beta brefl ⟩
         (ƛ (ƛ (comp · (comp · (subst (up (dimap Φ₂)) (vs (vs vz)) id · id · var (vs vz)) · var vz) · (subst (up (dimap Φ₁)) (vs (vs vz)) id · var (vs vz) · id))) · id)
       ⟷⟨ equiv (cong₂ (λ i1 i2 → (ƛ (ƛ (comp · (comp · (i1 · id · var (vs vz)) · var vz) · (i2 · var (vs vz) · id))) · id)) (subst-up (dimap Φ₂) (vs (vs vz)) id) (subst-up (dimap Φ₁) (vs (vs vz)) id)) ⟩
        (ƛ (ƛ (comp · (comp · (up (dimap Φ₂) · id · var (vs vz)) · var vz) · (up (dimap Φ₁) · var (vs vz) · id))) · id)
       ⟷⟨ beta ⟩  
         ƛ (comp · (comp · (subst (up (dimap Φ₂)) (vs vz) id · id · id) · var vz)
            · (subst (up (dimap Φ₁)) (vs vz) id · id · id))
       ⟷⟨ equiv (cong₂ (λ i1 i2 →  ƛ (comp · (comp · (i1 · id · id) · var vz) · (i2 · id · id))) (subst-up (dimap Φ₂) (vs vz) id) (subst-up (dimap Φ₁) (vs vz) id)) ⟩
         ƛ (comp · (comp · (up (dimap Φ₂) · id · id) · var vz) · (up (dimap Φ₁) · id · id))
       ⟷⟨ brefl ⟩
         ƛ (comp · (comp · (up (dimap Φ₂ · idε · idε)) · var vz) · (up (dimap Φ₁ · idε · idε)))
       ⟷⟨ congƛ (congApp (congApp brefl (congApp (congApp brefl (congUp (dimapid Φ₂))) brefl)) (congUp (dimapid Φ₁))) ⟩
         ƛ (comp · (comp · id · var vz) · id)
       ⟷⟨ β≡ (β≡ brefl) ⟩
         _
       ⟷⟨ congƛ eta ⟩
         idε
       ∎


  dimapcomp : ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
                → (f1 : ε ⊢ (τ₃ ⇒ τ₂)) → (f2 : ε ⊢ (τ₂ ⇒ τ₃)) →  (g1 : ε ⊢ (τ₂ ⇒ τ₁)) →  (g2 : ε ⊢ (τ₁ ⇒ τ₂)) 
                → (dimap Φ · f1 · f2 ∘ dimap Φ · g1 · g2) βη-≡ (dimap Φ · (g1 ∘ f1) · (f2 ∘ g2))
  dimapcomp Id f1 f2 g1 g2 = β≡ brefl
  dimapcomp (Φ₁ ⟶ Φ₂) f1 f2 g1 g2 =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin 
         (dimap (Φ₁ ⟶ Φ₂) · f1 · f2 ∘ dimap (Φ₁ ⟶ Φ₂) · g1 · g2)
       ⟷⟨ β≡ brefl ⟩
         (dimap (Φ₁ ⟶ Φ₂) · f1 · f2 ∘ dimap (Φ₁ ⟶ Φ₂) · g1 · g2)
       ⟷⟨ {!!} ⟩
         (dimap (Φ₁ ⟶ Φ₂) · (g1 ∘ f1) · (f2 ∘ g2))
       ∎ -}
{-
module FunctorEnv where
  open Functor
  
  data Ftx : Set where
    ε : Ftx
    _▸_ : Ftx → Functor → Ftx

  ⟦_⟧Γ : Ftx → Ty → Ctx
  ⟦ ε ⟧Γ v = ε
  ⟦ φ ▸ Φ ⟧Γ v = ⟦ φ ⟧Γ v ▸ ⟦ Φ ⟧Φ v
-}

{-
id : ∀ {Γ a} → Γ ⊢ (a ⇒ a)
id = up (ƛ var)

comp : ∀ {Γ a b c} → Γ ⊢ ((b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
comp = up (ƛ (ƛ (ƛ (lf (lf var) · (lf var · var)))))

infixl 2 _∘_
_∘_ : ∀ {a b c Γ} → Γ ⊢ (b ⇒ c) → Γ ⊢ (a ⇒ b) → Γ ⊢ (a ⇒ c)
t1 ∘ t2 = comp · t1 · t2

module Functor where

  infixr 4 _⟶_

  data Functor : Set where
    Id   : Functor
    _⟶_ : (Φ₁ Φ₂ : Functor) → Functor

  ⟦_⟧Φ_ : Functor → Ty → Ty
  ⟦ Id ⟧Φ       τ = τ
  ⟦ Φ₁ ⟶ Φ₂ ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ

  dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ ((a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a)
  dimap Id         = ƛ (ƛ var)
  dimap (Φ₁ ⟶ Φ₂) = ƛ (ƛ (ƛ (up (dimap Φ₂) · lf (lf var) · lf var ∘ var ∘ up (dimap Φ₁) · lf var · lf (lf var) )))


  dimapid : ∀ {τ} → (Φ : Functor) → ⟦ dimap {τ} {τ} Φ · id · id ⟧ ≡ ⟦ id ⟧
  dimapid Id  = refl
  dimapid {a} (Φ₁ ⟶ Φ₂) = {!!}

  dimapcomp : ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
                → (f1 : ε ⊢ τ₃ ⇒ τ₂) → (f2 : ε ⊢ τ₂ ⇒ τ₃) →  (g1 : ε ⊢ τ₂ ⇒ τ₁) →  (g2 : ε ⊢ τ₁ ⇒ τ₂) 
                → ⟦ dimap Φ · f1 · f2 ∘ dimap Φ · g1 · g2 ⟧ ≡ ⟦ dimap Φ · (g1 ∘ f1) · (f2 ∘ g2) ⟧
  dimapcomp Id f1 f2 g1 g2 = refl
  dimapcomp (Φ₁ ⟶ Φ₂) f1 f2 g1 g2 = cong₂ (λ v1 v2 → λ ρ x x' → v1 ρ (x (v2 ρ x'))) 
                                             (dimapcomp Φ₂ f1 f2 g1 g2) (dimapcomp Φ₁ g2 g1 f2 f1)


module FunctorEnv where
  open Functor
  
  data Ftx : Set where
    ε : Ftx
    _▸_ : Ftx → Functor → Ftx

  ⟦_⟧Γ : Ftx → Ty → Ctx
  ⟦ ε ⟧Γ v = ε
  ⟦ φ ▸ Φ ⟧Γ v = ⟦ φ ⟧Γ v ▸ ⟦ Φ ⟧Φ v
-}
{-
module TTS (A : Ty) (R : Ty) (rep : ε ⊢ A ⇒ R) (abs : ε ⊢ R ⇒ A) where
  open Functor
  open FunctorEnv

  data _∶_⊨_↝_ : (φ : Ftx) → (Φ : Functor) → ⟦ φ ⟧Γ A ⊢ ⟦ Φ ⟧Φ A → ⟦ φ ⟧Γ R ⊢ ⟦ Φ ⟧Φ R → Set where
    var : ∀ {Φ} → (ε ▸ Φ) ∶ Φ ⊨ var ↝ var
    _·_ : ∀ {φ Φ₁ Φ₂ e₁ e₁' e₂ e₂'} 
               → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ e₁ ↝ e₁' → φ ∶ Φ₁ ⊨ e₂ ↝ e₂' 
               → φ ∶ Φ₂ ⊨ (e₁ · e₂) ↝ (e₁' · e₂')
    lam   : ∀ {φ Φ₁ Φ₂ e e'} → (φ ▸ Φ₁) ∶ Φ₂ ⊨ e ↝ e' → φ ∶ (Φ₁ ⟶ Φ₂) ⊨ ƛ e ↝ ƛ e'

  module Proof (rep-abs : ⟦ abs ∘ rep ⟧ ≡ ⟦ id ⟧) where

    θ : (φ : Ftx) → Env (⟦ φ ⟧Γ A) → Env (⟦ φ ⟧Γ R)
    θ ε         ε         = ε
    θ (y ▸ y')  (a ► a') = θ y a ► ⟦ dimap y' · abs · rep ⟧ ε a'
  
    under : {f g : Set → Set} → ∀ {x} → f x ≡ g x → (\a → f a) ≡ (\a → g a)
    under = {!!}
    
    mutual
      tts-prop : ∀ {φ Φ e e'} {ρ : Env (⟦ φ ⟧Γ A)} → φ ∶ Φ ⊨ e ↝ e' → ⟦ up (dimap Φ · rep · abs) · e' ⟧ (θ φ ρ) ≡ ⟦ e ⟧ ρ
      tts-prop {.(ε ▸ Φ)} {Φ} {ρ = env} var with env
      ... | ε ► r = 
            begin
              ⟦ dimap Φ · rep · abs ∘ dimap Φ · abs · rep ⟧ ε r
            ≡⟨ cong (λ v → v ε r) (dimapcomp Φ rep abs abs rep) ⟩
              ⟦ dimap Φ · (abs ∘ rep) · (abs ∘ rep) ⟧ ε r
            ≡⟨ cong₂ (λ v1 v2 → ⟦ dimap Φ ⟧ ε (v1 ε) (v2 ε) r) rep-abs rep-abs ⟩
              ⟦ dimap Φ · id · id ⟧ ε r
            ≡⟨ cong (λ v → v ε r) (dimapid Φ) ⟩
              r
            ∎
      tts-prop (y · y') = {!!}
      tts-prop {φ} {Φ₁ ⟶ Φ₂} {ƛ e1} {ƛ e2} {ρ} (lam y) =
         let prem : (λ x → ⟦ e1 ⟧ (ρ ► x)) ≡ (λ x → ⟦ up (dimap Φ₂ · rep · abs) · e2 ⟧ (θ (φ ▸ Φ₁) (ρ ► x)))
             prem = {!cong!}
         in begin
              ⟦ up (dimap (Φ₁ ⟶ Φ₂) · rep · abs) · ƛ e2 ⟧ (θ φ ρ)
            ≡⟨ {!!} ⟩
              (λ x → ⟦ up (dimap Φ₂ · rep · abs) · e2 ⟧ (θ (φ ▸ Φ₁) (ρ ► x)))
            ≡⟨ {!cong (\v → (\x → v)) (tts-prop {φ ▸ Φ₁} {Φ₂} {e1} {e2} {ρ ► x} y)!} ⟩
              (λ x → ⟦ e1 ⟧ (ρ ► x))
            ≡⟨ refl ⟩
              ⟦ ƛ e1 ⟧ ρ
            ∎
      -- tts-prop : ∀ {φ Φ e e'} {ρ : Env (⟦ φ ⟧Γ A)} → φ ∶ Φ ⊨ e ↝ e' → ⟦ up (dimap Φ · rep · abs) · e' ⟧ (θ φ ρ) ≡ ⟦ e ⟧ ρ
-}