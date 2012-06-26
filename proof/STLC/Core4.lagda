\begin{code}
{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --termination-depth=2 #-}
module STLC.Core4 where

open import Data.Nat
import Data.Bool
import Data.Fin
import Data.List
import Data.Product
import Data.String
import Data.Vec
import Data.AVL.Sets
import Data.AVL.IndexedMap
import Function
import Relation.Nullary
import Relation.Binary
import Relation.Binary.PropositionalEquality
import Level

module LambdaCalculus where

  open Data.Fin hiding (_+_; lift)
  open Data.Vec
  open import Category.Applicative.Indexed
  open import Data.Vec.Properties
  open Relation.Binary.PropositionalEquality
  open Function

  infixl 5 _!_

  data Lam (n : ℕ) : Set where
    var : (i : Fin n) → Lam n
    _!_ : (s t : Lam n) → Lam n
    lam : (t : Lam (suc n)) → Lam n

  Comb : Set
  Comb = Lam 0

  v : {m : ℕ} (n : ℕ) → Lam (suc (n + m))
  v n = var (inject+ _ (fromℕ n))

  S : Comb
  S = lam (lam (lam ((v 2 ! v 0) ! (v 1 ! v 0))))

  K : Comb
  K = lam (lam (v 1))

  I : Comb
  I = lam (v 0)

  Y : Comb
  Y = lam (lam (v 1 ! (v 0 ! v 0)) ! lam (v 1 ! (v 0 ! v 0)))

  CC : Comb
  CC = lam (lam (lam (v 2 ! (v 1 ! v 0))))

  -- Weakening a lambda term.
  wk : {n : ℕ} → Lam n → Lam (suc n)
  wk (var i) = var (inject₁ i)
  wk (s ! t) = wk s ! wk t
  wk (lam t) = lam (wk t)

  wkℕ : ∀ {m n} → Lam n → Lam (m + n)
  wkℕ {zero} l = l
  wkℕ {suc n} l = wk (wkℕ {n} l)

  infixl 2 _·_
  _·_ : ∀ {n} → Lam n → Lam n → Lam n
  g · f = lam (wk g ! (wk f ! v 0))

  Subst : ℕ → ℕ → Set
  Subst m n = Vec (Lam n) m

  -- Extending an existing substitution.
  infixl 3 _∣_
  _∣_ : {m n : ℕ} →
       Lam n → Subst m n → Subst (suc m) n
  _∣_ = _∷_

  -- Mapping over a substitution
  smap : {m n o : ℕ} → (Lam n → Lam o) → Subst m n → Subst m o
  smap f = Data.Vec.map f

  -- Shifts a finite number:
  --
  --   shift m n = suc n     if m <= n
  --   shift m n = n         otherwise
  --
  shift : (m : ℕ) → {n : ℕ} → Fin n → Fin (suc n)
  shift zero    n       = suc n
  shift (suc m) zero    = zero
  shift (suc m) (suc n) = suc (shift m n)

  -- Shifting by a sufficiently large offset does not affect
  -- the number being shifted.
  shift-inv : {n : ℕ} (i : Fin n) → shift n i ≡ inject₁ i
  shift-inv zero    = refl
  shift-inv (suc i) = cong suc (shift-inv i)

  -- Lifting a lambda term. Similar to weaking, but
  -- where weakening does not change the numbers of the
  -- variables, lifting increments each free variable by one.
  -- The extra counter keeps track of the number of bound
  -- variables.
  lf : (m : ℕ) → {n : ℕ} → Lam n → Lam (suc n)
  lf m (var n) = var (shift m n)
  lf m (s ! t) = lf m s ! lf m t
  lf m (lam t) = lam (lf (suc m) t)

  lift : {n : ℕ} → Lam n → Lam (suc n)
  lift = lf 0

  -- Lifting a closed term does not change the term.
  lf-closed : {n : ℕ} (t : Lam n) → lf n t ≡ wk t
  lf-closed (var i) = cong var (shift-inv i)
  lf-closed (s ! t) = cong₂ _!_ (lf-closed s) (lf-closed t)
  lf-closed (lam t) = cong lam (lf-closed t)

  -- Identity substitution
  ι : (n : ℕ) → Subst n n
  ι zero    = []
  ι (suc n) = v 0 ∣ smap lift (ι n)

  -- Characterizing the identity substitution.
  -- NOT FOR GRADING, JUST FOR FUN.
  ι-lookup : {n : ℕ} (i : Fin n) → lookup i (ι n) ≡ var i
  ι-lookup zero    = refl
  ι-lookup {suc n} (suc i) =
        let open Morphism (lookup-morphism i)
        in begin
             lookup (suc i) (ι (suc n))
           ≡⟨ refl ⟩
             lookup i (replicate lift ⊛ ι n)
           ≡⟨ op-⊛ (replicate lift) (ι n) ⟩
             lookup i (replicate lift) (lookup i (ι n))
           ≡⟨ cong (lookup i (replicate lift)) (ι-lookup i) ⟩
             (lookup i ∘ replicate $ lift) (var i)
           ≡⟨ cong (λ x → x (var i)) (op-pure lift) ⟩
             lift (var i)
           ≡⟨ refl ⟩
             var (suc i)
           ∎
    where open ≡-Reasoning


  -- Simultaneous substitution.
  -- Idea: Substitute all variables in one go.
  ssubst : {m n : ℕ} → Lam m → Subst m n → Lam n
  ssubst (var i) φ = lookup i φ
  ssubst (s ! t) φ = ssubst s φ ! ssubst t φ
  ssubst (lam t) φ = lam (ssubst t (v 0 ∣ smap lift φ))

  -- Identity substitution really is the identity.
  -- NOT FOR GRADING, JUST FOR FUN.
  ι-ssubst : {n : ℕ} (t : Lam n) → ssubst t (ι n) ≡ t
  ι-ssubst (var i) = ι-lookup i
  ι-ssubst (s ! t) = cong₂ _!_ (ι-ssubst s) (ι-ssubst t)
  ι-ssubst {n} (lam t) = cong lam (ι-ssubst t) 

  -- Beta-reduction
  β : {n : ℕ} → Lam (suc n) → Lam n → Lam n
  β s t = ssubst s (t ∣ ι _)

  ⟦_⟧ : ∀ {n} → Lam n → Lam n
  ⟦ var i ⟧ = var i
  ⟦ s ! t ⟧ with ⟦ s ⟧ | ⟦ t ⟧
  ⟦ s ! t ⟧ | lam f | a = β f a
  ⟦ s ! t ⟧ | f | a = f ! a
  ⟦ lam t ⟧ = lam ⟦ t ⟧

module Functor where

  open LambdaCalculus
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  infixr 4 _⟶_

  data Functor : Set where
    Id   : Functor
    _⟶_ : (Φ₁ Φ₂ : Functor) → Functor
{-
  ⟦_⟧Φ_ : Functor → Ty → Ty
  ⟦ Id ⟧Φ       τ = τ
  ⟦ Φ₁ ⟶ Φ₂ ⟧Φ τ = ⟦ Φ₁ ⟧Φ τ ⇒ ⟦ Φ₂ ⟧Φ τ
-}
  dimap : (Φ : Functor) → Lam 0
  dimap Id         = lam (lam (v 0))
  dimap (Φ₁ ⟶ Φ₂) = 
    lam (lam (lam (wk (wk (wk (dimap Φ₂))) ! v 2 ! v 1 · v 0 · wk (wk (wk (dimap Φ₁))) ! v 1 ! v 2 )))

  dimapid : ∀ {x} → (Φ : Functor) → ⟦ dimap Φ ! I ! I ! x ⟧ ≡ ⟦ x ⟧
  dimapid Id  = refl
  dimapid {x} (Φ₁ ⟶ Φ₂) = 
              begin
               {!!}
              ≡⟨ {!refl!} ⟩
               ⟦ x ⟧
              ∎

  -- Small-step reduction of lambda calculus
{-  infixl 4 _⟶_

  data _⟶_ {n : ℕ} : Lam n → Lam n → Set where
    left  : {t₁ t₂ t : Lam n} →
            t₁ ⟶ t₂ → t₁ ! t ⟶ t₂ ! t
    right : {t₁ t₂ t : Lam n} →
            t₁ ⟶ t₂ → t ! t₁ ⟶ t ! t₂
    lam   : {t₁ t₂   : Lam (suc n)} →
            t₁ ⟶ t₂ → lam t₁ ⟶ lam t₂
    beta  : {t₁ : Lam (suc n)} {t₂ : Lam n} →
            lam t₁ ! t₂ ⟶ β t₁ t₂

  Ω : Comb
  Ω = lam (v 0 ! v 0) ! lam (v 0 ! v 0)

  Ω-loops : Ω ⟶ Ω
  Ω-loops = beta
-}
module Types where
  
  data BaseType : Set where
    bool : BaseType
    int  : BaseType

  infixr 6 _⇒_
  data Type : Set where
    con : (α : BaseType) → Type
    _⇒_ : (τ₁ τ₂ : Type) → Type

\end{code}
