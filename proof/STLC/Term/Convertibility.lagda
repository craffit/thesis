%if False
\begin{code}
module STLC.Term.Convertibility where

open import Relation.Binary hiding (_⇒_)
open import STLC.Variable
open import STLC.Term.Base
open import STLC.Term.Inject
open import STLC.Term.Operations.Weaken
open import STLC.Term.Operations.Simultaneous
open import Util.PropositionalEquality
import Relation.Binary.EqReasoning

infixl 7 _⟷_
infix 1 _βη-≡_
infix 1 _βη-=>_
infixl 3 _%·_
infixl 8 _%/-_
infixl 8 _-%/_
infixl 8 _%/_
\end{code}
%endif

The semantics of stlc terms can be related using a convertibility relation. The $\beta\eta$-convertibility relation used here is based on work by Keller and Altenkirch~\cite{keller10}.

\begin{code}
data _βη-≡_ {Γ : Con} : {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → Set where
  □     : ∀ {σ} → {t : Γ ⊢ σ} → t βη-≡ t
  bsym  : ∀ {σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  _⟷_  : ∀ {σ} → {t₁ t₂ t₃ : Γ ⊢ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  %Λ_   : ∀ {σ τ} → {t₁ t₂ : Γ , σ ⊢ τ} → t₁ βη-≡ t₂ → Λ t₁ βη-≡ Λ t₂
  _%·_  : ∀ {σ τ} → {t₁ t₂ : Γ ⊢ σ ⇒ τ} → {u₁ u₂ : Γ ⊢ σ} 
        → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ →  t₁ · u₁ βη-≡ t₂ · u₂
  beta  : ∀ {σ τ} → {t : Γ , σ ⊢ τ} → {u : Γ ⊢ σ} → Λ t · u βη-≡ t / sub vz u
  eta   : ∀ {σ τ} → {t : Γ ⊢ σ ⇒ τ} → Λ (weaken t · v 0) βη-≡ t
\end{code}

The first three constructors establish reflexivity, symmetry and transitivity of $\beta\eta$-equality. |%Λ_| and |_%·_| establishes that convertibility is a congruence relation. |beta| and |eta| represent the respective beta-redutcion and eta-expansion rules. Note that because of the use of well-typed deBruijn indices, the subject reduction property of the lambda calculus comes for free. $\beta$-reduction is guaranteed to preserve typing.

%if False
\begin{code}
data _βη-=>_ {Δ : Con} : {Γ : Con} → Γ => Δ → Γ => Δ → Set where
  sz : sz βη-=> sz
  ss : ∀ {Γ τ} {s1 s2 : Γ => Δ} {t1 t2 : Δ ⊢ τ} 
     → s1 βη-=> s2 → t1 βη-≡ t2 → ss s1 t1 βη-=> ss s2 t2

=>refl : ∀ {Γ Δ} {s : Γ => Δ} → s βη-=> s
=>refl {.ε} {Δ} {sz} = sz
=>refl {Γ , τ} {Δ} {ss y y'} = ss (=>refl {Γ} {Δ} {y}) □

=>sym : ∀ {Γ Δ} {s s' : Γ => Δ} → s βη-=> s' → s' βη-=> s
=>sym sz = sz
=>sym (ss y y') = ss (=>sym y) (bsym y')

=>trans : ∀ {Γ Δ} {s s' s'' : Γ => Δ} → s βη-=> s' → s' βη-=> s'' → s βη-=> s''
=>trans sz p2 = p2
=>trans (ss y y') (ss y0 y1) = ss (=>trans y y0) (y' ⟷ y1)
\end{code}
%endif

Because the $\beta\eta$-convertibility relation is reflexive, symmetric and transitive, it gives rise to a setoid. In Agda this makes the relation eligible for use with the equational reasoninging module, which makes proving properties much more intuitive. As an example, the |ext| property shows that this formalization of the lambda calculus supports and the extensionality lemma.

\begin{code}
βηsetoid : {Γ : Con} {σ : Ty} → Setoid _ _
βηsetoid {Γ} {σ} = 
  record { Carrier = Γ ⊢ σ 
         ; _≈_ = _βη-≡_
         ; isEquivalence = 
              record { refl  = □
                     ; sym   = bsym
                     ; trans = _⟷_
                     }                              
         }
\end{code}

%if False
\begin{code}
βη=>setoid : {Γ Δ : Con} → Setoid _ _
βη=>setoid {Γ} {Δ} = 
  record { Carrier = Γ => Δ 
         ; _≈_ = _βη-=>_
         ; isEquivalence = 
              record { refl  = =>refl
                     ; sym   = =>sym
                     ; trans = =>trans
                     }                              
         }

-- Congruences of βη-≡

□' : ∀ {Γ τ} (t : Γ ⊢ τ) → t βη-≡ t
□' _ = □

%≡_ : ∀ {Γ σ} → {t₁ t₂ : Γ ⊢ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
%≡_ refl = □

=>≡ : ∀ {Γ Δ} → {t1 t2 : Γ => Δ} → t1 ≡ t2 → t1 βη-=> t2
=>≡ refl = =>refl

%wkTm : ∀ {Γ σ τ} → (x : Γ ∋ σ) → {u₁ u₂ : Γ - x ⊢ τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
%wkTm _ □ = □
%wkTm x (bsym p) = bsym (%wkTm x p)
%wkTm x (p₁ ⟷ p₂) = %wkTm x p₁ ⟷ %wkTm x p₂
%wkTm x (%Λ p) = %Λ %wkTm (vs x) p
%wkTm x (p₁ %· p₂) = %wkTm x p₁ %· %wkTm x p₂
%wkTm x {Λ t · u} beta =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ %≡ (■' (wkTm (vs x) t) ≡/ ≡ss (sym (wkExtS-I x)) refl) ⟩
       _ ⟷⟨ %≡ wk-ext/ (vs x) t (var x) (ss (wkS x I) (wkTm x u)) ⟩
       _  ⟷⟨ %≡ wk/ x t (ss I u) ⟩
       _ ∎
%wkTm x {._} {t} eta = %Λ (%≡ sym (wkTmExcvz x t) %· □) ⟷ eta

%lookup : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → s βη-=> s' → (y : Γ ∋ τ) → lookup y s βη-≡ lookup y s'
%lookup {ε} sz ()
%lookup {y , .τ} {Δ} {τ} (ss y0 y1) vz = y1
%lookup {y , y'} (ss y0 y1) (vs y2) = %lookup y0 y2

%extS : ∀ {Γ Δ τ} {t t' : Δ ⊢ τ} → (v : Γ ∋ τ) → {s s' : Γ - v => Δ} → s βη-=> s' → t βη-≡ t' → extS v t s βη-=> extS v t' s'
%extS vz s0 t0 = ss s0 t0
%extS (vs y) (ss y' y0) t0 = ss (%extS y y' t0) y0

%wkS : ∀ {Γ Δ τ}  → (v : Δ ∋ τ) → {s s' : Γ => Δ - v} → s βη-=> s' 
     → wkS v s βη-=> wkS v s'
%wkS v sz = sz
%wkS v (ss y y') = ss (%wkS v y) (%wkTm v y')

_%/-_ : ∀ {Γ Δ τ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → (s : Γ => Δ) → t / s βη-≡ t' / s
_%/-_ □ s = □
_%/-_ (bsym y) s = bsym (y %/- s)
_%/-_ (y ⟷ y') s = y %/- s ⟷ y' %/- s
_%/-_ (%Λ y) s = %Λ (y %/- (ss (wkS vz s) (var vz)))
_%/-_ (y %· y') s = y %/- s %· y' %/- s
_%/-_ (beta {_} {_} {t} {u}) s =
    let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
       _ ⟷⟨ beta ⟩
       _ ⟷⟨ %≡ merge-/ t _ _ ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (wkS-extS/=> vz (u / s) s I) refl) ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (/=>I s) refl) ⟩
       _ ⟷⟨ %≡ (■' t ≡/ ≡ss (sym (I/=> s)) refl) ⟩
       _ ⟷⟨ %≡ split-/ t _ _ ⟩
      _ ∎
_%/-_ (eta {_} {_} {t}) s = %Λ (%≡ wk-wkExtS/ vz vz t s %· □) ⟷ eta

_-%/_ : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → (t : Γ ⊢ τ) → s βη-=> s' → t / s βη-≡ t / s'
_-%/_ (var y) s  = %lookup s y
_-%/_ (Λ y) s    = %Λ (y -%/ %extS vz (%wkS vz s) □)
_-%/_ (y · y') s = y -%/ s %· y' -%/ s

_%/_ : ∀ {Γ Δ τ} → {s s' : Γ => Δ} → {t t' : Γ ⊢ τ} → t βη-≡ t' → s βη-=> s'
    → t / s βη-≡ t' / s'
_%/_ {t' = t'} □ s = t' -%/ s
_%/_ (bsym y) s  = bsym (y %/ =>sym s)
_%/_ (y ⟷ y') s = y %/ s ⟷ y' %/ =>refl
_%/_ (%Λ y) s   = %Λ (y %/ (ss (%wkS vz s) □))
_%/_ (y %· y') s = y %/ s %· y' %/ s
_%/_ {s = s} {s' = s'} (beta {t = t} {u = u}) sb =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ beta ⟩
     _ ⟷⟨ %≡ merge-/ t _ _ ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (wkS-extS/=> vz (u / s) s I) refl) ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (/=>I s) refl) ⟩
     _ ⟷⟨ t -%/ ss sb (u -%/ sb) ⟩
     _ ⟷⟨ %≡ (■' t ≡/ ≡ss (sym (I/=> s')) refl) ⟩
     _ ⟷⟨ %≡ split-/ t _ _ ⟩
     _ ∎
_%/_ (eta {t = t}) s =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
     _ ⟷⟨ %Λ (%≡ wk-wkExtS/ vz vz t _ %· □) ⟩
     _ ⟷⟨ %Λ (%wkTm vz (t -%/ s) %· □) ⟩
     _ ⟷⟨ eta ⟩
     _ ∎
\end{code}
%endif

\begin{code}
ext : ∀ {Γ σ τ} → (e e' : Γ ⊢ σ ⇒ τ) → weaken e · v 0 βη-≡ weaken e' · v 0
    → e βη-≡ e'
ext e e' eq =
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
  in begin
       e
     ⟷⟨ bsym eta ⟩
       Λ (weaken e · v 0)
     ⟷⟨ %Λ eq ⟩
       Λ (weaken e' · v 0)
     ⟷⟨ eta ⟩
       e'
     ∎

\end{code}
