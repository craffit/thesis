\begin{code}
module Named where

open import Data.Empty
open import Data.Maybe
open import Data.Nat renaming (_≟_ to _≟n_)
open import Data.Product
open import Data.String renaming (_≟_ to _≟s_)
open import Function using (id)
open import Relation.Nullary
open import Category.Functor
open import Relation.Binary.PropositionalEquality

infixr 4 _⟶_
infix 6 _,_∶_
infix 5 _∶_∈_
infix 5 _∈_
infix 5 _n∈_
infix 3 _⊢_
infix 1 Λ_⇒_
infixl 9 _·_

data Ty : Set where
  C    : (n : ℕ) → Ty
  _⟶_ : (τ₁ τ₂ : Ty) → Ty

{-
data Con : Set where
  ε     : Con
  _,_∶_ : (Γ : Con) → (n : String) → (τ : Ty) → Con

data _∶_∈_ (n : String) (τ : Ty) : Con → Set where
  vz : ∀ {Γ} → n ∶ τ ∈ Γ , n ∶ τ
  vs : ∀ {Γ m σ} → (v : n ∶ τ ∈ Γ) → n ∶ τ ∈ Γ , m ∶ σ

data _∈_ (τ : Ty) : Con → Set where
  vz : ∀ {Γ n} → τ ∈ Γ , n ∶ τ
  vs : ∀ {Γ n σ} → (v : τ ∈ Γ) → τ ∈ Γ , n ∶ σ

data _n∈_ (n : String) : Con → Set where
  vz : ∀ {Γ τ} → n n∈ Γ , n ∶ τ
  vs : ∀ {Γ m τ} → (v : n n∈ Γ) → n n∈ Γ , m ∶ τ

data _⊢_ (Γ : Con) : Ty → Set where
  var   : ∀ {τ} → (v : τ ∈ Γ) → Γ ⊢ τ
  Λ_⇒_  : ∀ {σ τ} → (n : String) → (t : Γ , n ∶ σ ⊢ τ) → Γ ⊢ σ ⟶ τ
  _·_ : ∀ {σ τ} → Γ ⊢ σ ⟶ τ → Γ ⊢ σ → Γ ⊢ τ

M : {A : Set} → Maybe A → Set
M {A} (just x) = A
M nothing = ⊥

findτ : (Γ : Con) → (n : String) → Maybe (∃ \τ → τ ∈ Γ)
findτ ε n = nothing
findτ (Γ , n ∶ τ) n' with n ≟s n'
findτ (Γ , n ∶ τ) n' | yes p = just (τ , vz)
findτ (Γ , n ∶ τ) n' | no ¬p = 
  let open RawFunctor functor
  in map id vs <$> findτ Γ n'

ftype : ∀ {Γ n} → (x : M (findτ Γ n)) → Ty
ftype {Γ} {n} w with findτ Γ n
ftype {Γ} w | just (τ , v) = τ
ftype ()    | nothing


v : ∀ {Γ} → (n : String) → {x : M (findτ Γ n)} → Γ ⊢ ftype {Γ} {n} x
v {Γ} n with findτ Γ n
v n      | just (τ , v) = var v
v n {()} | nothing

idf : ∀ {Γ τ} → Γ ⊢ τ ⟶ τ
idf {Γ} {τ} = Λ "x" ⇒ v {_} "x" {τ , vz}
-}

data Con : Set where
  ε     : Con
  _,_∶_ : (Γ : Con) → (n : ℕ) → (τ : Ty) → Con

data _∶_∈_ (n : ℕ) (τ : Ty) : Con → Set where
  vz : ∀ {Γ} → n ∶ τ ∈ Γ , n ∶ τ
  vs : ∀ {Γ m σ} → (v : n ∶ τ ∈ Γ) → n ∶ τ ∈ Γ , m ∶ σ

data _∈_ (τ : Ty) : Con → Set where
  vz : ∀ {Γ n} → τ ∈ Γ , n ∶ τ
  vs : ∀ {Γ n σ} → (v : τ ∈ Γ) → τ ∈ Γ , n ∶ σ

data _n∈_ (n : ℕ) : Con → Set where
  vz : ∀ {Γ τ} → n n∈ Γ , n ∶ τ
  vs : ∀ {Γ m τ} → (v : n n∈ Γ) → n n∈ Γ , m ∶ τ

data _⊢_ (Γ : Con) : Ty → Set where
  var   : ∀ {τ} → (v : τ ∈ Γ) → Γ ⊢ τ
  Λ_⇒_  : ∀ {σ τ} → (n : ℕ) → (t : Γ , n ∶ σ ⊢ τ) → Γ ⊢ σ ⟶ τ
  _·_ : ∀ {σ τ} → Γ ⊢ σ ⟶ τ → Γ ⊢ σ → Γ ⊢ τ

M : {A : Set} → Maybe A → Set
M {A} (just x) = A
M nothing = ⊥

findτ : (Γ : Con) → (n : ℕ) → Maybe (∃ \τ → τ ∈ Γ)
findτ ε n = nothing
findτ (Γ , n ∶ τ) n' with n ≟n n'
findτ (Γ , n ∶ τ) n' | yes p = just (τ , vz)
findτ (Γ , n ∶ τ) n' | no ¬p = 
  let open RawFunctor functor
  in map id vs <$> findτ Γ n'

ftype : ∀ {Γ n} → (x : M (findτ Γ n)) → Ty
ftype {ε} ()
ftype {Γ , n ∶ τ} {n'} x  with n ≟n n'
ftype {Γ , n ∶ τ} (proj₁ , proj₂) | yes p = proj₁
ftype {Γ , n ∶ τ} {nm} x' | no ¬p with findτ Γ nm | inspect (findτ Γ) nm
ftype {Γ , n' ∶ τ} {nm} x' | no ¬p | just x | [ eq ] = ftype {Γ} {nm} (subst M (sym eq) x)
ftype {Γ , n' ∶ τ} () | no ¬p | nothing | eq


v : ∀ {Γ} → (n : ℕ) → {x : M (findτ Γ n)} → Γ ⊢ ftype {Γ} {n} x
v {Γ} n {x} = {!!}

idf : ∀ {Γ τ} → Γ ⊢ τ ⟶ τ ⟶ τ
idf {Γ} {τ} = Λ 1 ⇒ (Λ 1 ⇒ v 1 {_ , vs vz})

\end{code}