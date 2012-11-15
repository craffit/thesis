\begin{code}
module Let.Types where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_) renaming (_-_ to _-F_)
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality

open IsCommutativeSemiring isCommutativeSemiring hiding (zero ; sym ; refl)
open IsCommutativeMonoid +-isCommutativeMonoid hiding (sym ; refl)
open SemiringSolver
-- open IsSemigroup isSemigroup

data Ty : ℕ → Set where
  var : ∀ {n} → Fin n → Ty n
  ○   : ∀ {n} → Ty n
  _⇒_ : ∀ {n} → Ty n → Ty n → Ty n

wkT : ∀ {n} → Ty n → Ty (suc n)
wkT (var y)  = var (suc y)
wkT ○        = ○
wkT (y ⇒ y') = wkT y ⇒ wkT y

data Sch (m : ℕ) (n : ℕ) : Set where
  S : Ty (m + n) → Sch m n

wkS : ∀ {m n} → Sch m n → Sch m (suc n)
wkS {m} {n} (S t) = S {m} {suc n} (subst Ty ((solve 2 (\m n → con 1 :+ (m :+ n) := m :+ (con 1 :+ n)) refl) m n) (wkT t))

data Con : Set where
  ε    : Con
  _►_  : ∀ {m n} → Con → Sch m n → Con

{-
wkCon : ∀ {n} → Con n → Con (suc n)
wkCon ε         = ε
wkCon (y ► y') = wkCon y ► wkS y'
-}

data _=>_ : ℕ → ℕ → Set where
  ε    : ∀ {m} → 0 => m
  _►_  : ∀ {n m} → n => m → Ty m → suc n => m

wk=> : ∀ {m n} → m => n → m => suc n
wk=> ε = ε
wk=> (y ► y') = wk=> y ► wkT y'

ext=> : ∀ {m n} → m => n → Ty n → suc m => n
ext=> s t = s ► t

lookup : ∀ {n m} → Fin n → n => m → Ty m
lookup {zero} () s
lookup {suc n} zero (y ► y') = y'
lookup {suc n} (suc i) (y ► y') = lookup i y

lookup-wk : ∀ {n m} → (i : Fin n) → (s : n => m) → (t : Ty m) 
          → lookup i s ≡ t → lookup i (wk=> s) ≡ wkT t
lookup-wk () ε t p
lookup-wk zero (y ► .t) t refl = refl
lookup-wk (suc i) (y ► y') t p = lookup-wk i y t p

_/t_ : ∀ {n m} → Ty n → n => m → Ty m
var y /t s    = lookup y s
○ /t s        = ○
(y ⇒ y') /t s = (y /t s) ⇒ (y' /t s)

ι : ∀ {n} → n => n
ι {zero}  = ε
ι {suc n} = wk=> ι ► var zero

lookupι : ∀ {n} → (y : Fin n) → lookup y ι ≡ var y
lookupι zero = refl
lookupι (suc i) = lookup-wk i ι (var i) (lookupι i)

/tι : ∀ {n} → (t : Ty n) → t /t ι ≡ t
/tι (var y)  = lookupι y
/tι ○        = refl
/tι (y ⇒ y') = cong₂ _⇒_ (/tι y) (/tι y')

_++_ : ∀ {m n o} → m => n → o => n → (m + o) => n
ε ++ s         = s
(y ► y') ++ s = (y ++ s) ► y' 

gen : ∀ {m n} → Ty (m + n) → Sch m n
gen {m} {n} = S {m} {n}

inst : ∀ {m n} → Sch m n → m => n → Ty n
inst {m} {n} (S t) s = t /t (s ++ ι)

_∪_ : ∀ {n} → Ty n → Ty n → Maybe (n => n)
var y ∪ t = {!!}
○ ∪ t = {!!}
(y ⇒ y') ∪ t = {!!}

data _∋_ : {m n : ℕ} → Con → Sch m n → Set where
  vz : ∀ {m n} {Γ : Con} {τ : Sch m n} → (Γ ► τ) ∋ τ
  vs : ∀ {m m' n n'} {Γ : Con} {t : Sch m n} {t' : Sch m' n'} → Γ ∋ t → (Γ ► t') ∋ t


_-_ : ∀ {m n} {σ : Sch m n} → (Γ : Con) → Γ ∋ σ → Con
ε       - ()
(Γ ► σ) - vz     = Γ
(Γ ► τ) - (vs x) = (Γ - x) ► τ

wkv : ∀ {Γ m m' n n'} {σ : Sch m n} {τ : Sch m' n'} → (x : Γ ∋ σ) → (Γ - x) ∋ τ → Γ ∋ τ
wkv vz     y       = vs y
wkv (vs x) vz      = vz
wkv (vs x) (vs y)  = vs (wkv x y)

{-
wkTm : ∀ {σ Γ τ} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm x (var v)    = var (wkv x v)
wkTm x (Λ t)      = Λ (wkTm (vs x) t)
wkTm x (t₁ · t₂)  = wkTm x t₁ · wkTm x t₂
-}


data _⊢_ {n : ℕ} : Con → Ty n → Set where
  lt  : ∀ {m} {c : Con} {t : Ty n} {t' : Ty (m + n)} → (x : c ⊢ t') → (c ► S {m} {n} t') ⊢ t → c ⊢ t
  Λ   : {c : Con} {t : Ty n} {t' : Ty n} → (c ► S {zero} {n} t') ⊢ t → c ⊢ (t' ⇒ t)
  var : ∀ {m} {c : Con} {t : Sch m n} → c ∋ t → (i : m => n) → c ⊢ inst t i
  _·_ : {c : Con} {t t' : Ty n} → c ⊢ (t' ⇒ t) → c ⊢ t' → c ⊢ t

wkTm : ∀ {Γ m n n'} {σ : Sch m n} {τ : Ty n'} → (x : Γ ∋ σ) → (Γ - x) ⊢ τ → Γ ⊢ τ
wkTm x (lt x' y) = lt (wkTm x x') (wkTm (vs x) y)
wkTm x (Λ y) = Λ (wkTm (vs x) y)
wkTm x (var y i) = var (wkv x y) i
wkTm x (y · y') = wkTm x y · wkTm x y' 

id : {t : Ty 1} → (e : ε ⊢ t) → ε ⊢ t
id {t} e = lt {_} {1} {_} (Λ {_} {_} {_} {var zero} (var vz ε)) (var vz (ε ► t) · wkTm vz e)


{-
_∪_ : ∀ {n m} → Ty n → Ty m → Maybe (n => m)
var y ∪ t' = {!!}
○ ∪ var y = nothing
○ ∪ ○ = {!!}
○ ∪ (y ⇒ y') = nothing
(y ⇒ y') ∪ t' = {!!}
-}
\end{code}