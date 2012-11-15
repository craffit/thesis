%if False
\begin{code}
module TTS.Functor where

open import STLC
open import Data.Maybe
open import Category.Monad

import Relation.Binary.EqReasoning

infixr 4 _⟶_
\end{code}
%endif

With the object language laid out, we move on to develop a representation for |(TTS(stlc))| in Agda. Essential to this type and transform system is the typing functor. The typing functor is defined as a straightforward inductive datatype as follows:

\begin{code}
data Functor : Set where
  Id   : Functor
  K    : (τ : Ty) → Functor
  _⟶_  : (Φ₁ Φ₂ : Functor) → Functor
\end{code}

The |Id| constructor represents the hole in the functor and the |K| constructor represents a constant type from the object language. Function space is represented by |_⟶_|. The functor data type is essentially a universe type for functors. We can interpret this universe as types in the object language, using the following interpretation function:

\begin{code} 
⟦_⟧Φ_ : Functor → Ty → Ty
⟦ Id       ⟧Φ τ = τ
⟦ K σ      ⟧Φ τ = σ     
⟦ Φ₁ ⟶ Φ₂  ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ
\end{code}

The functor interpretation function takes a functor and a type to fill into the holes and constructs a type in the object language. Using this interpretation on the type level, we can also construct an accompanying term-level functor for the object language. 

\begin{code}
dimap : ∀ {a b} → (Φ : Functor) → ε ⊢ (a ⇒ b) ⇒ (b ⇒ a) ⇒ ⟦ Φ ⟧Φ b ⇒ ⟦ Φ ⟧Φ a
dimap Id         = Λ (Λ (v 0))
dimap (K τ)      = Λ (Λ id)
dimap (Φ₁ ⟶ Φ₂)  = Λ (Λ (Λ (up (dimap Φ₂) · v 2 · v 1 ∘ v 0 ∘ up (dimap Φ₁) · v 1 · v 2)))
\end{code}

%if False
\begin{code}
-- Helper function to expand the definition of dimap
dimap-const : ∀ {Γ a b σ} → (ab : ε ⊢ a ⇒ b) → (re : ε ⊢ b ⇒ a) → (v : Γ ⊢ σ)
            → up (dimap (K σ) · ab · re) · v βη-≡ v
dimap-const ab re v =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %up β≡ brefl %· □ ⟩
     _ ⟷⟨ up-id-id v ⟩
     _ ∎

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
       _ ⟷⟨ %≡ comm-/-/=> (dimap Φ₂ · f1 · f2) _ _ %∘ □ %∘ %≡ comm-/-/=> (dimap Φ₁ · f2 · f1) _ _ ⟩
       _ ⟷⟨ bsym (%≡ up-/sz _) %∘ □ %∘ bsym (%≡ up-/sz _) ⟩
       _ ∎
\end{code}
%endif

To show that we have constructed a proper functor, we can now give proof of the functor laws. The functor laws are formulated as follows:



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
dimapcomp :  ∀ {τ₁ τ₂ τ₃} → (Φ : Functor) 
             → (f1 : ε ⊢ τ₃ ⇒ τ₂) → (f2 : ε ⊢ τ₂ ⇒ τ₃) 
             → (g1 : ε ⊢ τ₂ ⇒ τ₁) → (g2 : ε ⊢ τ₁ ⇒ τ₂) 
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

\begin{code}
_* : Functor → Maybe Ty
Id * = nothing
K τ * = just τ
(Φ₁ ⟶ Φ₂) * =
  let open RawMonadPlus monadPlus
  in _⇒_ <$> Φ₁ * ⊛ Φ₂ *
\end{code}

%if False
\begin{code}
open import Relation.Binary.PropositionalEquality
open import STLC.Congruence
\end{code}
%endif

\begin{code}
*-Ty : ∀ {Φ τ σ} → just τ ≡ Φ * → ⟦ Φ ⟧Φ σ ≡ τ 
\end{code}

%if False
\begin{code}
*-Ty {Id} ()
*-Ty {K τ} refl = refl
*-Ty {Φ₁ ⟶ Φ₂} p with Φ₁ * | inspect (_*) Φ₁ | Φ₂ * | inspect (_*) Φ₂
*-Ty {Φ₁ ⟶ Φ₂} {.(x ⇒ x')} {σ} refl | just x | [ eq ] | just x' | [ eq' ] = cong₂ _⇒_ (*-Ty {Φ₁} {x} {σ = σ} (sym eq)) (*-Ty {Φ₂} {x'} {σ = σ} (sym eq'))
*-Ty {Φ₁ ⟶ Φ₂} () | just x | w | nothing | w2
*-Ty {Φ₁ ⟶ Φ₂} () | nothing | w | r2 | w2

open import Data.Product

*-split : ∀ {Φ Φ' τ} → just τ ≡ (Φ ⟶ Φ') * 
      → Σ Ty (\g → Σ Ty (\t → (just g ≡ Φ *) × (just t ≡ Φ' *) × (τ ≡ g ⇒ t)))
*-split {Φ} {Φ'} p with Φ * | Φ' * 
*-split refl | just x | just x' = x , (x' , (refl , (refl , refl)))
*-split () | just x | nothing
*-split () | nothing | r2

*-≡τ : ∀ {Φ τ σ} → just τ ≡ Φ * → ⟦ Φ ⟧Φ σ ≡τ τ 
*-≡τ {Id} ()
*-≡τ {K τ} refl = ≡τrefl
*-≡τ {Φ₁ ⟶ Φ₂} p with *-split {Φ₁} {Φ₂} p
*-≡τ {Φ₁ ⟶ Φ₂} p | x , (x' , (eq , (eq' , refl))) = *-≡τ {Φ₁} eq ⇒ *-≡τ {Φ₂} eq'

*-eq≡τ :  ∀ {Φ τ a b} → just τ ≡ Φ * → ⟦ Φ ⟧Φ a ≡τ ⟦ Φ ⟧Φ b
*-eq≡τ {Φ} p = ≡τtrans (*-≡τ {Φ} p) (≡τsym (*-≡τ {Φ} p))

int>⊢ : ∀ {Γ τ} → {t : Γ ⊢ τ} → t βη-≡ ! ≡Γrefl , ≡τrefl >⊢ t
int>⊢ {t = t} = bsym (%≡ !,⊢-id ≡Γrefl ≡τrefl t)

-- Lemma showing that a dimap on a complete functor yields the identity.
{-
*-id : ∀ {Φ τ a b} → (p : just τ ≡ Φ *) 
     → dimap {a} {b} Φ 
     βη-≡ ! ε , ≡τrefl ⇒ ≡τrefl ⇒ ≡τrefl ⇒ *-eq≡τ {Φ} p >⊢ Λ (Λ (up idε))
*-id {Id} ()
*-id {K τ} refl with ≡τ-eq-refl (≡τtrans ≡τrefl (≡τsym (≡τrefl {τ})))
... | x = %Λ (%Λ (%Λ bsym (%≡ cong var (!,∋vz ((ε , (≡τrefl ⇒ ≡τrefl)) , (≡τrefl ⇒ ≡τrefl)) ≡τrefl (≡τtrans ≡τrefl (≡τsym ≡τrefl))))))
*-id {Φ₁ ⟶ Φ₂} p with *-split {Φ₁} {Φ₂} p
*-id {Φ₁ ⟶ Φ₂} {.(x ⇒ x')} {a} {b} p | x , (x' , (eq , (eq' , refl))) =  
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %Λ (%Λ (%Λ (%up *-id {Φ₂} {x'} eq' %· □ %· □ %∘ □ %∘ %up *-id {Φ₁} {x} {b} eq %· □ %· □))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (bsym (%≡ !,⊢up ≡Γrefl (≡τrefl ⇒ ≡τrefl ⇒ ≡τrefl ⇒ *-eq≡τ {Φ₂} eq') (Λ (Λ (Λ (var vz))))) %· □ %· □ %∘ □ %∘ bsym (%≡ !,⊢up ≡Γrefl (≡τrefl ⇒ ≡τrefl ⇒ ≡τrefl ⇒ *-eq≡τ {Φ₁} eq) (Λ (Λ (Λ (var vz))))) %· □ %· □))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (□ %· int>⊢ %· int>⊢ %∘ int>⊢ %∘ (□ %· int>⊢ %· int>⊢)))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (cong-!>⊢ ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ₂} eq') (Λ (Λ (Λ (var vz))) · v 2 · v 1) (Λ (var vz)) (β≡ brefl) %∘ □ %∘ cong-!>⊢ ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ₁} eq) (Λ (Λ (Λ (var vz))) · v 1 · v 2) (Λ (var vz)) (β≡ brefl)))) ⟩
--     _ ⟷⟨ %Λ (%Λ (%Λ {!!})) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ bsym eta)) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ do-comp _ _ _))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ (□ %· (bsym (%≡ (!,⊢wkTmvz ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ₁} eq) ≡τrefl (Λ (var vz)))) %· int>⊢) ⟷ cong-!>⊢ ≡Γrefl (*-eq≡τ {Φ₁} eq) _ _ (id-id (var vz)))))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ do-comp _ _ _))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ (bsym (%≡ !,⊢wkTmvz ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ₂} eq') ≡τrefl (Λ (var vz))) %· int>⊢)))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ cong-!>⊢ ≡Γrefl (*-eq≡τ {Φ₂} eq') _ _ (id-id (! ≡Γrefl , ≡τrefl >⊢ var (vs vz) · ! ≡Γrefl , *-eq≡τ {Φ₁} eq >⊢ var vz))))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ (cong-!>⊢ ≡Γrefl (≡τrefl ⇒ *-eq≡τ {Φ₂} eq') _ _ (bsym (int>⊢ {t = var (vs vz)})) %· bsym (int>⊢ {t = ! ≡Γrefl , *-eq≡τ {Φ₁} eq >⊢ (var vz)}))))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ %≡ !,⊢· ≡Γrefl (*-eq≡τ {Φ₁} eq) (*-eq≡τ {Φ₂} eq') (var (vs vz)) (var vz)))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%Λ (□ %· bsym int>⊢) ⟷ eta))) ⟩
     _ ⟷⟨ %Λ (%Λ (%Λ (%≡ cong (λ v' → ! ≡Γrefl , v' ⇒ *-eq≡τ {Φ₂} eq' >⊢ var vz) (≡τ-eq-eq _ _)))) ⟩
      _ ∎
-}
\end{code}
%endif