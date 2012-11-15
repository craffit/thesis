\begin{code}
module Let.Infer where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_) renaming (_-_ to _-F_)
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Props renaming (_≟_ to _≟F_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary

open IsCommutativeSemiring isCommutativeSemiring hiding (zero ; refl) renaming (sym to +sym)
open IsCommutativeMonoid +-isCommutativeMonoid hiding (sym ; refl)
open SemiringSolver
-- open IsSemigroup isSemigroup

open ≡-Reasoning 
open import Function

infixr 6 _⇒_
infixl 5 _►_
infix 4 _∋_

infix 2 _⊢_
-- infixl 10 _·_

-- infixl 5 _-_

infix 3 _=>_                                                                                              
infix 8 _/t_

data Ty : ℕ → Set where
  var : ∀ {n} → Fin n → Ty n
  ○   : ∀ {n} → Ty n
  _⇒_ : ∀ {n} → Ty n → Ty n → Ty n

inj⇒l : ∀ {n} {t1 t2 t3 t4 : Ty n} → t1 ⇒ t2 ≡ t3 ⇒ t4 → t1 ≡ t3
inj⇒l refl = refl

inj⇒r : ∀ {n} {t1 t2 t3 t4 : Ty n} → t1 ⇒ t2 ≡ t3 ⇒ t4 → t2 ≡ t4
inj⇒r refl = refl

injvar : ∀ {n} {a b : Fin n} → (_≡_ {_} {Ty n} (var a) (var b)) → a ≡ b
injvar refl = refl

_≟τ_ : {n : ℕ} → Decidable {A = Ty n} _≡_
var y ≟τ var y' with y ≟F y'
var y ≟τ var y' | yes p = yes (cong var p)
var y ≟τ var y' | no ¬p = no (λ x → ¬p (injvar x))
var y ≟τ ○ = no (λ ())
var y ≟τ (y' ⇒ y0) = no (λ ())
○ ≟τ var y = no (λ ())
○ ≟τ ○ = yes refl
○ ≟τ (y ⇒ y') = no (λ ())
(y ⇒ y') ≟τ var y0 = no (λ ())
(y ⇒ y') ≟τ ○ = no (λ ())
(y ⇒ y') ≟τ (y0 ⇒ y1) with y ≟τ y0 | y' ≟τ y1
(y ⇒ y') ≟τ (y0 ⇒ y1) | yes p | yes p' = yes (cong₂ _⇒_ p p')
(y ⇒ y') ≟τ (y0 ⇒ y1) | yes p | no ¬p = no (λ refl' → ¬p (inj⇒r refl'))
(y ⇒ y') ≟τ (y0 ⇒ y1) | no ¬p | yes p = no (λ refl' → ¬p (inj⇒l refl'))
(y ⇒ y') ≟τ (y0 ⇒ y1) | no ¬p | no ¬p' = no (λ refl' → ¬p (inj⇒l refl'))

wkTv : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
wkTv zero v            = suc v
wkTv (suc i) zero      = zero
wkTv (suc i) (suc i')  = suc (wkTv i i')

widenTopTv : ∀ {n} → (m : ℕ) → Fin n → Fin (m + n)
widenTopTv zero v = v
widenTopTv {n} (suc n') v = wkTv (fromℕ (n' + n)) (widenTopTv n' v)

widenBotTv : ∀ {n} → (m : ℕ) → Fin n → Fin (m + n)
widenBotTv zero v = v
widenBotTv (suc n') v = wkTv zero (widenTopTv n' v)

mapT : ∀ {n m} → (Fin n → Fin m) → Ty n → Ty m
mapT f (var y) = var (f y)
mapT f ○ = ○
mapT f (y ⇒ y') = mapT f y ⇒ mapT f y'

mapT-id : ∀ {n} x → mapT {n} id x ≡ id x
mapT-id (var y) = refl
mapT-id ○ = refl
mapT-id (y ⇒ y') = cong₂ _⇒_ (mapT-id y) (mapT-id y') 

wkT : ∀ {n} → Fin (suc n) → Ty n → Ty (suc n)
wkT v = mapT (wkTv v)

widenTopT : ∀ {n} → (m : ℕ) → Ty n → Ty (m + n)
widenTopT v = mapT (widenTopTv v)

widenBotT : ∀ {n} → (m : ℕ) → Ty n → Ty (m + n)
widenBotT v = mapT (widenBotTv v)

data Con (n : ℕ) : Set where
  ε    : Con n
  _►_  : Con n → Ty n → Con n

mapCon : ∀ {m n } → (Fin n → Fin m) → Con n → Con m
mapCon f ε = ε
mapCon f (y ► y') = mapCon f y ► mapT f y'

{-
wkCon : ∀ {n} → Con n → Con (suc n)
wkCon ε         = ε
wkCon (y ► y') = wkCon y ► wkS y'
-}

data _=>_ : ℕ → ℕ → Set where
  ε    : ∀ {m} → 0 => m
  _►_  : ∀ {n m} → n => m → Ty m → suc n => m

map=> : ∀ {m n o} → (Fin n → Fin o) → m => n → m => o
map=> f ε = ε
map=> f (y ► y') = map=> f y ► mapT f y'

wk=> : ∀ {m n} → Fin (suc n) → m => n → m => suc n
wk=> n = map=> (wkTv n)

ext=> : ∀ {m n} → m => n → Fin (suc m) → Ty n → suc m => n
ext=> s zero t = s ► t
ext=> ε (suc ()) t
ext=> (y ► y') (suc i) t = ext=> y i t ► y' 

lookup : ∀ {n m} → Fin n → n => m → Ty m
lookup {zero} () s
lookup {suc n} zero (y ► y') = y'
lookup {suc n} (suc i) (y ► y') = lookup i y

lookup-map : ∀ {n m o} → (i : Fin n) → (s : n => m) → (t : Ty m) → (f : Fin m → Fin o)  
          → lookup i s ≡ t → lookup i (map=> f s) ≡ mapT f t
lookup-map () ε t f p
lookup-map zero (y ► .t) t f refl = refl
lookup-map (suc i) (y ► y') t f p = lookup-map i y t f p
{-
lookup-wk : ∀ {n m} → (i : Fin n) → (s : n => m) → (t : Ty m) 
          → lookup i s ≡ t → lookup i (wk=> s) ≡ wkT t
lookup-wk () ε t p
lookup-wk zero (y ► .t) t refl = refl
lookup-wk (suc i) (y ► y') t p = lookup-wk i y t p
-}
_/t_ : ∀ {n m} → Ty n → n => m → Ty m
var y /t s    = lookup y s
○ /t s        = ○
(y ⇒ y') /t s = (y /t s) ⇒ (y' /t s)

_/c_ : ∀ {n m} → Con n → n => m → Con m
ε /c s2 = ε
(y ► y') /c s2 = y /c s2 ► y' /t s2


wkT-wk=>lookup : ∀ {n m} → (v : Fin (suc m)) → (s : n => m) → (y : Fin n) → wkT v (lookup y s) ≡ lookup y (wk=> v s)
wkT-wk=>lookup {zero} v s ()
wkT-wk=>lookup {suc n} v (y ► y') zero = refl
wkT-wk=>lookup {suc n} v (y ► y') (suc i) = wkT-wk=>lookup v y i

wkT-wk=>/ : ∀ {n m} → (v : Fin (suc m)) → (s : n => m) → (t : Ty n) → wkT v (t /t s) ≡ t /t wk=> v s
wkT-wk=>/ v s (var y) = wkT-wk=>lookup v s y
wkT-wk=>/ v s ○ = refl
wkT-wk=>/ v s (y ⇒ y') = cong₂ _⇒_ (wkT-wk=>/ v s y) (wkT-wk=>/ v s y')

_/s_ : ∀ {n m o} → n => m → m => o → n => o
ε /s s2 = ε
(y ► y') /s s2 = y /s s2 ► y' /t s2

wk-ext-lookup : ∀ {n m} → (v : Fin (suc n)) → (y : Fin n) → (t' : Ty m) → (s : n => m) → lookup (wkTv v y) (ext=> s v t') ≡ lookup y s
wk-ext-lookup {zero} v () t' s
wk-ext-lookup {suc n} zero zero t' (y ► y') = refl
wk-ext-lookup {suc n} (suc i) zero t' (y ► y') = refl
wk-ext-lookup {suc n} zero (suc i) t' (y ► y') = refl
wk-ext-lookup {suc n} (suc i) (suc i') t' (y ► y') = wk-ext-lookup i i' t' y

wk-ext-/t : ∀ {n m} → (v : Fin (suc n)) → (t : Ty n) → (t' : Ty m) → (s : n => m) → wkT v t /t ext=> s v t' ≡ t /t s
wk-ext-/t v (var y) t' s = wk-ext-lookup v y t' s
wk-ext-/t v ○ t' s = refl
wk-ext-/t v (y ⇒ y') t' s = cong₂ _⇒_ (wk-ext-/t v y t' s) (wk-ext-/t v y' t' s)

wk-ext-/s : ∀ {n m o} → (v : Fin (suc m)) → (t : Ty o) → (s1 : n => m) → (s2 : m => o) → wk=> v s1 /s ext=> s2 v t ≡ s1 /s s2
wk-ext-/s v t ε s2 = refl
wk-ext-/s v t (y ► y') s2 = cong₂ _►_ (wk-ext-/s v t y s2) (wk-ext-/t v y' t s2)

lookup-comm-/ : ∀ {m n o} → (y : Fin m) → (x : m => n) → (x' : n => o) → lookup y (x /s x') ≡ lookup y x /t x'
lookup-comm-/ {zero} () ε x'
lookup-comm-/ {suc n} zero (y ► y') x' = refl
lookup-comm-/ {suc n} (suc i) (y ► y') x' = lookup-comm-/ i y x'

comm-/ : ∀ {m n o} → (t1 : Ty m) → (x : m => n) → (x' : n => o) → t1 /t x /s x' ≡ (t1 /t x) /t x'
comm-/ (var y) x x' = lookup-comm-/ y x x'
comm-/ ○ x x' = refl
comm-/ (y ⇒ y') x x' = cong₂ _⇒_ (comm-/ y x x') (comm-/ y' x x')

ι : ∀ {n} → n => n
ι {zero}  = ε
ι {suc n} = wk=> zero ι ► var zero


lookupι : ∀ {n} → (y : Fin n) → lookup y ι ≡ var y
lookupι zero = refl
lookupι {suc n} (suc i) = lookup-map i ι (var i) (wkTv zero) (lookupι {n} i)

/tι : ∀ {n} → (t : Ty n) → t /t ι ≡ t
/tι (var y)  = lookupι y
/tι ○        = refl
/tι (y ⇒ y') = cong₂ _⇒_ (/tι y) (/tι y')

/cι : ∀ {n} → (c : Con n) → c /c ι ≡ c
/cι ε = refl
/cι (y ► y') = cong₂ _►_ (/cι y) (/tι y')

/sι : ∀ {n m} → (s : n => m) → s /s ι ≡ s
/sι ε = refl
/sι (y ► y') = cong₂ _►_ (/sι y) (/tι y')

ι/s : ∀ {n m} → (s : n => m) → ι /s s ≡ s
ι/s ε = refl
ι/s (y ► y') = cong (λ v → v ► y') (subst (λ v → v ≡ y) (sym (wk-ext-/s zero y' ι y)) (ι/s y))

_++_ : ∀ {m n o} → m => n → o => n → (m + o) => n
ε ++ s         = s
(y ► y') ++ s = (y ++ s) ► y' 

data _∋_ {n : ℕ} : Con n → Ty n → Set where
  vz : {Γ : Con n} {τ : Ty n} → (Γ ► τ) ∋ τ
  vs : {Γ : Con n} {t t' : Ty n} → Γ ∋ t → (Γ ► t') ∋ t

map∋ : ∀ {n m} {c : Con n} {t : Ty n} → (f : Fin n → Fin m) → c ∋ t → mapCon f c ∋ mapT f t
map∋ f vz = vz
map∋ f (vs y) = vs (map∋ f y)

data _⊢_ {n : ℕ} : Con n → Ty n → Set where
  lam : {c : Con n} {t : Ty n} {t' : Ty n} → (c ► t') ⊢ t → c ⊢ (t' ⇒ t)
  var : {c : Con n} {t : Ty n} → c ∋ t → c ⊢ t
  app : {c : Con n} {t t' : Ty n} → c ⊢ (t' ⇒ t) → c ⊢ t' → c ⊢ t

_-_ : ∀ {n} {σ : Ty n} → (Γ : Con n) → Γ ∋ σ → Con n
ε       - ()
(Γ ► σ) - vz     = Γ
(Γ ► τ) - (vs x) = (Γ - x) ► τ

wkv : ∀ {n} {Γ : Con n} {σ τ : Ty n} → (x : Γ ∋ σ) → (Γ - x) ∋ τ → Γ ∋ τ
wkv vz     y       = vs y
wkv (vs x) vz      = vz
wkv (vs x) (vs y)  = vs (wkv x y)


wkTm : ∀ {n} {Γ : Con n} {σ τ : Ty n} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm x (var v)    = var (wkv x v)
wkTm x (lam t)     = lam (wkTm (vs x) t)
wkTm x (app t₁ t₂)  = app (wkTm x t₁) (wkTm x t₂)


mapTm : ∀ {n m} {c : Con n} {t : Ty n} → (f : Fin n → Fin m) → c ⊢ t → mapCon f c ⊢ mapT f t
mapTm f (lam y) = lam (mapTm f y)
mapTm f (var y) = var (map∋ f y)
mapTm f (app y y') = app (mapTm f y) (mapTm f y')

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Category.Functor
open import Category.Monad

open import Relation.Nullary

{-
open RawFunctor functor
-- open RawMonad monad
open RawMonadPlus monadPlus
-}
{-
wkTv : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
wkTv zero v            = suc v
wkTv (suc i) zero      = zero
wkTv (suc i) (suc i')  = suc (wkTv i i')
-}

remv : ∀ {n} → (t : Fin (suc n)) → (t' : Fin (suc n)) → {w : t ≡ t' → ⊥} → Fin n
remv zero zero {w} with w refl
... | ()
remv {zero} zero (suc ())
remv {suc n} zero (suc i) = zero
remv (suc i) zero = i
remv {zero} (suc ()) (suc i')
remv {suc n} (suc i) (suc i') {w} = suc (remv {n} i i' {λ refl → w (cong suc refl)})

injF : ∀ {n} → {i j : Fin n} → (_≡_ {_} {Fin (suc n)} (suc i) (suc j)) → i ≡ j
injF {zero} {()} p
injF {suc n} {zero} {zero} p = refl
injF {suc n} {suc i} {zero} ()
injF {suc n} {zero} {suc i'} ()
injF {suc n} {suc .i'} {suc i'} refl = refl

wkTv-neq : ∀ {n} →  (i : Fin n) → (j : Fin (suc n)) → wkTv j i ≡ j → ⊥
wkTv-neq {zero} () j p
wkTv-neq {suc n} zero zero ()
wkTv-neq {suc n} zero (suc i) ()
wkTv-neq {suc n} (suc i) zero ()
wkTv-neq {suc n} (suc i) (suc i') p = wkTv-neq i i' (injF p)

injF-congsuc : ∀ {n} {i j : Fin n} → (a : i ≡ j) → injF (cong suc a) ≡ a
injF-congsuc {zero} {()} p
injF-congsuc {suc n} {zero} {zero} refl = refl
injF-congsuc {suc n} {suc i} {zero} ()
injF-congsuc {suc n} {zero} {suc i'} ()
injF-congsuc {suc n} {suc .i'} {suc i'} refl = refl

wkTv-remv : ∀ {n} →  (i : Fin n) → (j : Fin (suc n)) → {w : wkTv j i ≡ j → ⊥} → i ≡ remv (wkTv j i) j {w}
wkTv-remv {zero} () j
wkTv-remv {suc n} zero zero = refl
wkTv-remv {suc n} zero (suc i) = refl
wkTv-remv {suc n} (suc i) zero = refl
wkTv-remv {suc n} (suc i) (suc i') = cong suc (wkTv-remv i i')

data AllV {n : ℕ} (P : Fin n → Set) : Ty n → Set where
  var : {f : Fin n} → P f → AllV P (var f) 
  ○   : AllV {n} P ○
  _⇒_ : {t1 t2 : Ty n} → AllV P t1 → AllV P t2 → AllV P (t1 ⇒ t2)

remvτ : ∀ {n} → (τ : Ty (suc n)) → (v : Fin (suc n)) → {w : AllV (\x → x ≡ v → ⊥) τ} → Ty n
remvτ (var y) v {var y'}   = var (remv y v {y'})
remvτ ○ v                  = ○
remvτ (y ⇒ y') v {w1 ⇒ w2} = remvτ y v {w1} ⇒ remvτ y' v {w2}

occursvar : ∀ {n} → (v : Fin n) → (y : Fin n) → Dec (v ≡ y) → Maybe (AllV (\x → x ≡ v → ⊥) (var y))
occursvar v y (yes p) = nothing
occursvar v y (no ¬p) = just (var (\p → ¬p (sym p)))

occurs : ∀ {n} → (v : Fin n) → (τ : Ty n) → Maybe (AllV (\x → x ≡ v → ⊥) τ)
occurs v (var y) = occursvar v y (v ≟F y)
occurs v ○ = just ○
occurs v (y ⇒ y') =
  let open RawMonad monad 
  in  occurs v y >>= (λ x → occurs v y' >>= (λ y0 → return (x ⇒ y0)))

tryBindVar : ∀ {n} → (v : Fin (suc n)) → (t : Ty (suc n)) → Maybe (suc n => n)
tryBindVar v t = 
  let open RawMonad monad
  in occurs v t >>= \x → return (ext=> ι v (remvτ t v {x})) 

univar : ∀ {n} → (t1 : Ty (suc n)) → (t2 : Ty (suc n)) → Maybe (suc n => n)
univar (var y) t2 = tryBindVar y t2
univar ○ (var y) = tryBindVar y ○
univar ○ ○ = nothing
univar ○ (y ⇒ y') = nothing
univar (y ⇒ y') (var y0) = tryBindVar y0 (y ⇒ y')
univar (y ⇒ y') ○ = nothing
univar (y ⇒ y') (y0 ⇒ y1) =
  let open RawMonadPlus monadPlus
  in univar y y0 ∣ univar y' y1

univar-id : ∀ {n} → (t : Ty (suc n)) → univar t t ≡ nothing
univar-id (var y) with occursvar y y (y ≟F y)
univar-id (var y) | just (var y') with y' refl
... | ()
univar-id (var y) | nothing = refl
univar-id ○ = refl
univar-id (y ⇒ y') = 
  let open RawMonadPlus monadPlus
  in subst₂ (\v v' → (univar y y ∣ univar y' y') ≡ (v ∣ v')) (univar-id y) (univar-id y') refl

mutual
  unify : ∀ {n} → (t1 : Ty n) → (t2 : Ty n) → Maybe (n => n)
  unify t1 t2 = unify' t1 t2 (t1 ≟τ t2)
  
  unify' : ∀ {n} → (t1 : Ty n) → (t2 : Ty n) → Dec (t1 ≡ t2) → Maybe (n => n)
  unify' t1 t2 (yes p) = just ι
  unify' {zero} t1 t2 (no ¬p) = nothing
  unify' {suc n} t1 t2 (no ¬p) =
    let open RawMonad monad
    in univar t1 t2 >>= \x → unify (t1 /t x) (t2 /t x) >>= (λ y → return (wk=> zero (x /s y)))


open import Function
open import Data.Unit

mutual
  lem1 : ∀ {n} → {t1 t2 : Ty (suc n)} → (x : suc n => n) → (x' : n => n)
     → univar t1 t2 ≡ just x → unify (t1 /t x) (t2 /t x) ≡ just x'
     → t1 /t wk=> zero (x /s x') ≡ t2 /t wk=> zero (x /s x')
  lem1 {n} {t1} {t2} x x' p p2 =
    begin
      t1 /t wk=> zero (x /s x')
    ≡⟨ sym (wkT-wk=>/ zero (x /s x') t1) ⟩
      _
    ≡⟨ cong (wkT zero) (comm-/ t1 x x') ⟩
      _
    ≡⟨ cong (wkT zero) (uni-e (t1 /t x) (t2 /t x) x' (sym p2)) ⟩
      _
    ≡⟨ sym (cong (wkT zero) (comm-/ t2 x x')) ⟩
      _
    ≡⟨ wkT-wk=>/ zero (x /s x') t2 ⟩
      t2 /t wk=> zero (x /s x')
    ∎

  uni-e : ∀ {n} → (t1 t2 : Ty n) → (s : n => n) → just s ≡ unify t1 t2 → t1 /t s ≡ t2 /t s
  uni-e t1 t2 s p with t1 ≟τ t2
  uni-e .t2 t2 .ι refl | yes refl = refl
  uni-e {zero} t1 t2 s () | no ¬p
  uni-e {suc n} t1 t2 s p | no ¬p with univar t1 t2 | inspect (univar t1) t2
  uni-e {suc n} t1 t2 s p | no ¬p | just x | [ eq ] with unify (t1 /t x) (t2 /t x) | inspect (unify (t1 /t x)) (t2 /t x)
  uni-e {suc n} t1 t2 .(wk=> zero (x /s x')) refl | no ¬p | just x | [ eq' ] | just x' | [ eq ] = lem1 {_} {t1} {t2} x x' eq' eq
  uni-e {suc n} t1 t2 s () | no ¬p | just x | [ eq ] | nothing | b
  uni-e {suc n} t1 t2 s () | no ¬p | nothing | v


{-
uni-split : ∀ {n} → (t1 t2 t3 t4 : Ty n) → (s1 s2 : n => n) 
          → unify t1 t2 ≡ just s1 → unify t3 t4 ≡ just s2 
          → unify (t1 ⇒ t3) (t2 ⇒ t4) ≡ just (s1 /s s2)
uni-split t1 t2 t3 t4 s1 s2 p1 p2 with t1 ≟τ t2 | t3 ≟τ t4
uni-split .t2 t2 .t4 t4 .ι .ι refl refl | yes refl | yes refl = cong just (sym (/sι ι))
uni-split {zero} .t2 t2 t3 t4 .ε s2 refl () | yes refl | no ¬p
uni-split {suc n} .t2 t2 t3 t4 .(map=> (λ v → suc v) ι ► var zero) s2 refl p2 | yes refl | no ¬p with univar t3 t4
uni-split {suc n} .t2 t2 t3 t4 .(map=> suc ι ► var zero) s2 refl p2 | yes refl | no ¬p | just x with unify (t3 /t x) (t4 /t x)
uni-split {suc n} .t2 t2 t3 t4 .(map=> suc ι ► var zero) s2 refl p2 | yes refl | no ¬p | just x | just x' = {!!}
uni-split {suc n} .t2 t2 t3 t4 .(map=> suc ι ► var zero) s2 refl () | yes refl | no ¬p | just x | nothing
{-  let open RawMonadPlus monadPlus
  in begin
     _ ≡⟨ cong
            (λ v →
               v ∣ just x >>=
               (λ x' →
                  unify (t2 /t x' ⇒ t3 /t x') (t2 /t x' ⇒ t4 /t x') >>=
                  (λ y → return (map=> suc (x' /s y)))))
            (univar-id t2) ⟩
     _ ≡⟨ {!!} ⟩
     _ ∎
-}
uni-split {suc n} .t2 t2 t3 t4 .(map=> suc ι ► var zero) s2 refl () | yes refl | no ¬p | nothing
uni-split {zero} t1 t2 t3 t4 s1 s2 () p2 | no ¬p | s
uni-split {suc n} t1 t2 .t4 t4 s1 .(map=> suc ι ► var zero) p1 refl | no ¬p | yes refl = {!!}
uni-split {suc n} t1 t2 t3 t4 s1 s2 p1 p2 | no ¬p | no ¬p' = {!!}
-}
uni-sym : ∀ {n} → (t1 t2 : Ty n) → unify t1 t2 ≡ unify t2 t1
uni-sym t1 t2 with unify t1 t2 | inspect (unify t1) t2
uni-sym t1 t2 | just x | [ eq ] = {!!}
uni-sym t1 t2 | nothing | w = {!!}

uni-id : ∀ {n} → (t : Ty n) → unify t t ≡ just ι
uni-id t with t ≟τ t
uni-id t | yes p = refl
uni-id t | no ¬p with ¬p refl
... | ()

uni-ext-left : ∀ {n} → (t1 t2 t : Ty n) → unify (t ⇒ t1) (t ⇒ t2) ≡ unify t1 t2
uni-ext-left t1 t2 t with t ≟τ t | t1 ≟τ t2
uni-ext-left t1 t2 t | yes p | yes p' = refl
uni-ext-left {zero} t1 t2 t | yes p | no ¬p = refl
uni-ext-left {suc n} t1 t2 t | yes p | no ¬p with univar t1 t2 | univar t t | univar-id t
uni-ext-left {suc n} t1 t2 t | yes p | no ¬p | just x | just x' | ()
uni-ext-left {suc n} t1 t2 t | yes p | no ¬p | just x | nothing | refl = 
  let open RawMonad monad
  in cong (\v → v >>= (\y → return (map=> suc (x /s y)))) (uni-ext-left {n} (t1 /t x) (t2 /t x) (t /t x))
uni-ext-left {suc n} t1 t2 t | yes p | no ¬p | nothing | just x | ()
uni-ext-left {suc n} t1 t2 t | yes p | no ¬p | nothing | nothing | r = refl
uni-ext-left t1 t2 t | no ¬p | r2 with ¬p refl
... | ()

widenTopTm : ∀ {n} {c : Con n} {t : Ty n} → (m : ℕ) → (c ⊢ t) → mapCon (widenTopTv m) c ⊢ mapT (widenTopTv m) t
widenTopTm m (lam y) = lam (widenTopTm m y)
widenTopTm m (var y) = var (map∋ (widenTopTv m) y)
widenTopTm m (app y y') = app (widenTopTm m y) (widenTopTm m y')

widenBotTm : ∀ {n} {c : Con n} {t : Ty n} → (m : ℕ) → (c ⊢ t) → mapCon (widenBotTv m) c ⊢ mapT (widenBotTv m) t
widenBotTm m (lam y) = lam (widenBotTm m y)
widenBotTm m (var y) = var (map∋ (widenBotTv m) y)
widenBotTm m (app y y') = app (widenBotTm m y) (widenBotTm m y')

_/∋_ : ∀ {n m} {c : Con n} {t : Ty n} → c ∋ t → (s : n => m) → c /c s ∋ t /t s
vz /∋ s = vz
vs y /∋ s = vs (y /∋ s)

_/tm_ : ∀ {n m} {c : Con n} {t : Ty n} → c ⊢ t → (s : n => m) → c /c s ⊢ t /t s
lam y /tm s = lam (y /tm s)
var y /tm s = var (y /∋ s)
app y y' /tm s = app (y /tm s) (y' /tm s)

!_>ty_ : ∀ {n m} → n ≡ m → Ty n → Ty m
! refl >ty t = t

!⇒ : ∀ {n m} {t1 t2 : Ty n} → (p : n ≡ m) → ! p >ty (t1 ⇒ t2) ≡ (! p >ty t1) ⇒ (! p >ty t2)
!⇒ refl = refl

!_>c_ : ∀ {n m} → n ≡ m → Con n → Con m
! refl >c c = c

!ε : ∀ {n m} → (p : n ≡ m) → ! p >c ε ≡ ε
!ε refl = refl

!► : ∀ {n m} {c : Con n} {t : Ty n} → (p : n ≡ m) → ! p >c (c ► t) ≡ (! p >c c) ► (! p >ty t)
!► refl = refl

!_>t_ : ∀ {n m} {c : Con n} {t : Ty n} → (p : n ≡ m) → c ⊢ t → ! p >c c ⊢ ! p >ty t
!_>t_ refl v = v

unifyTys : ∀ {n m} → Ty n → Ty m → Maybe (n + m => n + m)
unifyTys {n} {m} t1 t2 = 
  let t1' : Ty (n + m)
      t1' = ! comm m n >ty widenTopT m t1
      t2' : _
      t2' = widenBotT n t2
  in unify t1' t2'

unifyCons : ∀ {n} → Con n → Con n → Maybe (Con n × n => n)
unifyCons ε ε = just (ε , ι)
unifyCons {n} ε (y ► y') = just (y ► y' , ι)
unifyCons {n} (y ► y') ε = just (y ► y' , ι)
unifyCons {n} (y ► y') (y0 ► y1) =
  let open RawMonad monad
  in unifyCons y y0 >>= \ r → unify (y' /t proj₂ r) (y1 /t proj₂ r) >>= (λ s → return (((proj₁ r /c s) ► ((y' /t proj₂ r) /t s) , proj₂ r /s s)))

ext-Cons : ∀ {n}→ (c1 c2 c : Con n) → (s : n => n) → (just (c , s) ≡ unifyCons c1 c2) → (t : Ty n) → just (c ► t , s) ≡ unifyCons (c1 ► t) (c2 ► t)
ext-Cons c1 c2 c s p t =
  let open RawMonad monad
  in begin
     _ ≡⟨ cong₂ (λ v v' → just (v , v')) (sym (/cι (c ► t))) (sym (/sι s)) ⟩
     _ ≡⟨ {!!} ⟩
     _ ∎ 

uniCons-e-∋ : ∀ {n τ} → (c1 c2 c : Con n) → (s : n => n) → (just (c , s) ≡ unifyCons c1 c2) → (t : c1 ∋ τ) → c ∋ τ
uniCons-e-∋ ε c2 c s p ()
uniCons-e-∋ (y ► y') ε .(y ► y') .ι refl v = v
uniCons-e-∋ (y ► y') (y0 ► y1) c s p v with unifyCons y y0
uniCons-e-∋ (y ► y') (y0 ► y1) c s p v | just x with unify (y' /t proj₂ x) (y1 /t proj₂ x)
uniCons-e-∋ {n} {τ} (y ► .τ) (y0 ► y1) .(proj₁ /c x' ► (τ /t proj₂) /t x') .(proj₂ /s x') refl vz | just (proj₁ , proj₂) | just x' = {!!}
uniCons-e-∋ (y ► y') (y0 ► y1) .(proj₁ /c x' ► (y' /t proj₂) /t x') .(proj₂ /s x') refl (vs y2) | just (proj₁ , proj₂) | just x' = {!!}
uniCons-e-∋ (y ► y') (y0 ► y1) c s p v | just x | nothing = {!!}
uniCons-e-∋ (y ► y') (y0 ► y1) c s p v | nothing = {!!}

uniCons-e : ∀ {n τ} → (c1 c2 c : Con n) → (s : n => n) → (just (c , s) ≡ unifyCons c1 c2) → (t : c1 ⊢ τ) → c ⊢ τ
uniCons-e c1 c2 c s p (lam {.c1} {t} {t'} y) = lam (uniCons-e (c1 ► t') (c2 ► t') (c ► t') s (ext-Cons c1 c2 c s p t') y)
uniCons-e c1 c2 c s p (var y) = {!!}
uniCons-e c1 c2 c s p (app y y') = app (uniCons-e c1 c2 c s p y) (uniCons-e c1 c2 c s p y')

unifyApp : ∀ {n} → (ta t : Ty n) → (c1 c2 : Con n) → Maybe (Con n × n => n)
unifyApp ta t c1 c2 = 
  let open RawMonad monad
  in   unifyCons c1 c2
   >>= \s → unify (ta /t proj₂ s) (t /t proj₂ s) 
   >>= \s' → return (proj₁ s /c s' , proj₂ s /s s')

appArg : ∀ {n} → (ta t : Ty n) → (c1 c2 c : Con n) → (s : n => n)
    → unifyApp ta t c1 c2 ≡ just (c , s) → (tm : c1 ⊢ t) → c ⊢ (t /t s)
appArg ta .(t' ⇒ t) c1 c2 c s p (lam {.c1} {t} {t'} y)
  with unifyCons c1 c2 | inspect (unifyCons c1) c2
appArg (var y) .(t' ⇒ t) c1 c2 c s p (lam {.c1} {t} {t'} y') | just (proj₁ , proj₂) | [ eq ] = {!!}
appArg ○ .(t' ⇒ t) c1 c2 c s p (lam {.c1} {t} {t'} y) | just (proj₁ , proj₂) | [ eq ] = {!!}
appArg (y ⇒ y') .(t' ⇒ t) c1 c2 c s p (lam {.c1} {t} {t'} y0) | just (proj₁ , proj₂) | [ eq ]  with unify (y /t proj₂ ⇒ y' /t proj₂) (t' /t proj₂ ⇒ t /t proj₂) 
         | inspect (unify (y /t proj₂ ⇒ y' /t proj₂)) (t' /t proj₂ ⇒ t /t proj₂) 
appArg (y ⇒ y') .(t' ⇒ t) c1 c2 .(proj₁ /c x) .(proj₂ /s x) refl (lam {.c1} {t} {t'} z) | just (proj₁ , proj₂) | [ eq ] | just x | [ eq' ] = lam (appArg t' t (c1 ► t') proj₁ (proj₁ /c x ► t' /t proj₂ /s x) (proj₂ /s x) {!!} z) 
appArg (y ⇒ y') .(t' ⇒ t) c1 c2 c s () (lam {.c1} {t} {t'} z) | just (proj₁ , proj₂) | [ eq ] | nothing | r2
appArg ta .(t' ⇒ t) c1 c2 c s () (lam {.c1} {t} {t'} y) | nothing | r -- lam (appArg t' t (c1 ► t') c (c ► t' /t s) s {!!} y) 
appArg ta t c1 c2 c s p (var y) = {!!}
appArg ta t c1 c2 c s p (app {.c1} {.t} {t'} y y') with unifyCons c1 c2 | inspect (unifyCons c1) c2
appArg ta t c1 c2 c s p (app y y') | just (p₁ , p₂) | [ eq ] with 
  unify (ta /t p₂) (t /t p₂) | inspect (unify (ta /t p₂)) (t /t p₂)
appArg ta t c1 c2 .(p₁ /c x) .(p₂ /s x) refl (app {.c1} {.t} {t'} y y') | just (p₁ , p₂) | [ eq' ] | just x | [ eq ] =
  let open RawMonad monad
      lem : (((unifyCons c1 c2) >>= (\s' → unify (t' /t proj₂ s') (t' /t proj₂ s') 
            >>= (\s0 → return (proj₁ s' /c s0 , proj₂ s' /s s0)))) ≡ just (p₁ , p₂))
      lem = begin
            _ ≡⟨ cong
                   (λ v →
                      v >>=
                      (λ s' →
                         unify (t' /t proj₂ s') (t' /t proj₂ s') >>=
                         (λ s0 → return (proj₁ s' /c s0 , proj₂ s' /s s0))))
                   eq' ⟩
            _ ≡⟨ cong (λ v → v >>= (λ s0 → return (p₁ /c s0 , p₂ /s s0)))
                   (uni-id (t' /t p₂)) ⟩
            _ ≡⟨ cong₂ (λ v v' → just (v , v')) (/cι p₁) (/sι p₂) ⟩
            _ ∎
      lem2 : (((unifyCons c1 c2) >>= (\s' → unify ((t' ⇒ ta) /t proj₂ s') ((t' ⇒ t) /t proj₂ s') >>= (\s0 → return ((proj₁ s' /c s0) , (proj₂ s' /s s0))))) ≡ just (p₁ /c x , p₂ /s x))
      lem2 = begin
             _ ≡⟨ cong (\v → v >>= (\s' → unify ((t' ⇒ ta) /t proj₂ s') ((t' ⇒ t) /t proj₂ s') >>= (\s0 → return ((proj₁ s' /c s0) , (proj₂ s' /s s0))))) eq' ⟩
             _ ≡⟨ cong (λ v → v >>= (λ s0 → return (p₁ /c s0 , p₂ /s s0)))
                    (uni-ext-left (ta /t p₂) (t /t p₂) (t' /t p₂)) ⟩
             _ ≡⟨ cong (λ v → v >>= (λ s0 → return (p₁ /c s0 , p₂ /s s0))) eq ⟩
             _ ∎
  in app (appArg (t' ⇒ ta) (t' ⇒ t) c1 c2 (p₁ /c x) (p₂ /s x) lem2 y) 
         (subst (_⊢_ (p₁ /c x)) (sym (comm-/ t' p₂ x)) (appArg t' t' c1 c2 p₁ p₂ lem y' /tm x))
appArg ta t c1 c2 c s () (app y y') | just (proj₁ , proj₂) | [ eq ] | nothing | w 
appArg ta t c1 c2 c s () (app y y') | nothing | w 
{-
unifyτ : ∀ {n m} → Ty n → Ty n → Con n → Ty m → Con m → Set
unifyτ ta tr c1 t c2 = maybe′ (λ s → proj₁ s ⊢ proj₂ s) ⊤ (unifyTm ta tr c1 t c2)
-}
May : ∀ {n} → {A : Set n} → Maybe A → Set
May (just _) = ⊤
May nothing  = ⊥
{-
lemv : ∀ {n m} {ta tr : Ty n} {c1 : Con n} {t : Ty m} {c2 : Con m} {nc : Con (n + m)} 
     {s x' : n + m => n + m} → (t1 : c1 ⊢ ta ⇒ tr) → (t2 : c2 ⊢ t)
     → {eq : unifyCons (! comm m n >c mapCon (widenTopTv m) c1) (mapCon (widenBotTv n) c2) ≡ just (nc , s)}
     → {eq' : unify (! comm m n >ty widenTopT m ta /t s) (widenBotT n t /t s) ≡ just x'}
     → nc /c x' ⊢ (! comm m n >ty widenTopT m tr /t s) /t x'
lemv {n} {m} {ta} {tr} {ε} {t} {ε} {nc} {s} {x'} t1 t2 {eq} {eq'} with 
    subst (\v → unifyCons v ε ≡ just (nc , s)) (!ε (comm m n)) eq
lemv {n} {m} {ta} {tr} {ε} {t} {ε} {.ε} {.ι} {x'} t1 t2 {eq} {eq'} | refl = 
  app (subst₂ (\v v' → v /c ι ⊢ v' /t ι) (!ε (comm m n)) (!⇒ (comm m n)) (! comm m n >t widenTopTm m t1 /tm ι) /tm x') 
      (subst (\v → ε ⊢ v) (sym (uni-e (! comm m n >ty widenTopT m ta /t ι) (widenBotT n t /t ι) x' (sym eq'))) ((widenBotTm n t2 /tm ι) /tm x'))

{-=
     let p : _
         p = subst₂ (\v v1 → unify v v1 ≡ just {!!}) (/tι (! comm m n >ty mapT (widenTopTv m) ta)) (/tι (mapT (widenBotTv n) t)) eq'
     in {!!}
-}
lemv {n} {m} {ta} {tr} {y ► y'} {t} {ε} t1 t2 = {!!}
lemv {n} {m} {ta} {tr} {ε} {t} {y ► y'} t1 t2 = {!!}
lemv {n} {m} {ta} {tr} {y ► y'} {t} {y0 ► y1} {nc} {s} {x'} t1 t2 {eq} {eq'} with
     subst (\v → unifyCons v (mapCon (widenBotTv n) y0 ► mapT (widenBotTv n) y1) ≡ just (nc , s)) (!► (comm m n)) eq
... | v with 
     unifyCons (! comm m n >c mapCon (widenTopTv m) y) (mapCon (widenBotTv n) y0)
   | inspect (unifyCons (! comm m n >c mapCon (widenTopTv m) y)) (mapCon (widenBotTv n) y0)
lemv {n} {m} {ta} {tr} {y ► y'} {t} {y0 ► y1} t1 t2 | v | just x | [ eq ] with
     unify (! comm m n >ty mapT (widenTopTv m) y') (mapT (widenBotTv n) y1)
   | inspect (unify (! comm m n >ty mapT (widenTopTv m) y')) (mapT (widenBotTv n) y1)
lemv {n} {m} {ta} {tr} {y ► y'} {t} {y0 ► y1} {.(proj₁ /c x ► ! comm m n >ty widenTopT m y' /t x)} {.(proj₂ /s x)} {x'} t1 t2 | refl | just (proj₁ , proj₂) | [ eq ] | just x | [ eq' ] = {! !}
lemv {n} {m} {ta} {tr} {y ► y'} {t} {y0 ► y1} t1 t2 | () | just x | [ eq ] | nothing | w'
lemv {n} {m} {ta} {tr} {y ► y'} {t} {y0 ► y1} t1 t2 | () | nothing | w

{-  let t1' : mapCon (widenTopTv m) _ ⊢ mapT (widenTopTv m) _
      t1' = widenTopTm m t1
      t2' : mapCon (widenBotTv n) _ ⊢ mapT (widenBotTv n) _
      t2' = widenBotTm n t2
  in {!!} -}

_·_ : ∀ {n m} {c1 : Con n} {ta tr : Ty n} {c2 : Con m} {t' : Ty m}
    → (t1 : c1 ⊢ (ta ⇒ tr)) → (t2 : c2 ⊢ t') → unifyτ ta tr c1 t' c2
_·_ {n} {m} {c1} {ta} {tr} {c2} {t'} t1 t2 with unifyTm ta tr c1 t' c2 | inspect (unifyTm ta tr c1 t') c2
_·_ {n} {m} {c1} {ta} {tr} {c2} {t'} t1 t2 | just x | [ eq ] with 
    unifyCons (! comm m n >c mapCon (widenTopTv m) c1) (mapCon (widenBotTv n) c2)
  | inspect (unifyCons (! comm m n >c mapCon (widenTopTv m) c1)) (mapCon (widenBotTv n) c2)
_·_ {n} {m} {c1} {ta} {tr} {c2} {t'} t1 t2 | just x' | [ eq ] | just x | w  with 
    unify (! comm m n >ty mapT (widenTopTv m) ta /t proj₂ x) (mapT (widenBotTv n) t' /t proj₂ x)
  | inspect (unify (! comm m n >ty mapT (widenTopTv m) ta /t proj₂ x)) (mapT (widenBotTv n) t' /t proj₂ x)
_·_ {n} {m} {c1} {ta} {tr} t1 t2 | just .(nc /c x' , (! comm m n >ty mapT (widenTopTv m) tr /t s) /t x') | [ refl ] | just (nc , s) | [ eq' ] | just x' | [ eq ] = lemv t1 t2 {eq'} {eq}
t1 · t2 | just x' | [ () ] | just x | w | nothing | w'
t1 · t2 | just x | [ () ] | nothing | w
_·_ {n} {m} {c1} {ta} {tr} {c2} {t'} t1 t2 | nothing | w = tt
{-
_∪_ : ∀ {n m} → Ty n → Ty m → Maybe (n => m)
var y ∪ t' = {!!}
○ ∪ var y = nothing
○ ∪ ○ = {!!}
○ ∪ (y ⇒ y') = nothing
(y ⇒ y') ∪ t' = {!!}
-}-}
\end{code}