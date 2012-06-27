
%if False
\begin{code}

module STLC.Base where

\end{code}
%endif

\begin{code}

infixr 6 _⇒_

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _,_

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

infix 4 _∋_

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ σ} → Γ , σ ∋ σ
  vs : ∀ {τ Γ σ} → Γ ∋ σ → Γ , τ ∋ σ

\end{code}

\begin{code}

-- Removing a variable from a context
infixl 5 _-_

_-_ : {σ : Ty} → (Γ : Con) → Γ ∋ σ → Con
ε       - ()
(Γ , σ) - vz     = Γ
(Γ , τ) - (vs x) = (Γ - x) , τ

\end{code}

%if False
\begin{code}
-- Conversely, adding a variable to a context (weakening)

wkv : ∀ {Γ σ τ} → (x : Γ ∋ σ) → Γ - x ∋ τ → Γ ∋ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)


-- The equality between variables: the predicate...

data EqV {Γ : Con} : {σ τ : Ty} → Γ ∋ σ → Γ ∋ τ → Set where
  same : forall {σ} → {x : Γ ∋ σ} → EqV {Γ} {σ} {σ} x x
  diff : forall {σ τ} → (x : Γ ∋ σ) → (y : Γ - x ∋ τ) → EqV {Γ} {σ} {τ} x (wkv x y)


-- ... and the function that decides it

eq : forall {Γ σ τ} → (x : Γ ∋ σ) → (y : Γ ∋ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)
\end{code}
%endif

\begin{code}

infix 2 _⊢_
infixl 10 _·_

data _⊢_ : Con → Ty → Set where
  var : ∀ {Γ σ} → Γ ∋ σ → Γ ⊢ σ
  Λ   : ∀ {Γ σ τ} → Γ , σ ⊢ τ → Γ ⊢ σ ⇒ τ
  _·_ : ∀ {Γ σ τ} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ

\end{code}

\begin{code}

wkTm : ∀ {σ Γ τ} → (x : Γ ∋ σ) → Γ - x ⊢ τ → Γ ⊢ τ
wkTm x (var v) = var (wkv x v)
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (t₁ · t₂) = wkTm x t₁ · wkTm x t₂

weaken : ∀ {Γ τ σ} → Γ ⊢ τ → Γ , σ ⊢ τ
weaken t = wkTm vz t

\end{code}

%if False
\begin{code}

-- Substitutions for variables and terms

substVar : ∀ {σ Γ τ} → Γ ∋ τ → (x : Γ ∋ σ) → Γ - x ⊢ σ → Γ - x ⊢ τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x


subst : ∀ {σ Γ τ} → Γ ⊢ τ → (x : Γ ∋ σ) → Γ - x ⊢ σ → Γ - x ⊢ τ
subst (var v) x u = substVar v x u
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))
subst (t₁ · t₂) x u = subst t₁ x u · subst t₂ x u

open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst)
open ≡-Reasoning

-- Proofs that involve with

substSame2 : ∀ {Γ σ τ} → (x : _∋_ Γ σ) → eq x x ≡ same → eq (vs {τ} x) (vs x) ≡ same
substSame2 x p with eq x x
substSame2 x refl | .same = refl


substSame3 : ∀ {Γ σ} → (x : _∋_ Γ σ) → eq x x ≡ same
substSame3 vz = refl
substSame3 (vs x) = substSame2 x (substSame3 x)


substDiff2 : ∀ {Γ σ τ ρ} → (x : _∋_ Γ σ) → (y : _∋_ (Γ - x) τ) → eq x (wkv x y) ≡ diff x y → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
substDiff2 x y p with eq x (wkv x y)
substDiff2 x y refl | .(diff x y) = refl


substDiff3 : ∀ {Γ σ τ} → (x : _∋_ Γ σ) → (y : _∋_ (Γ - x) τ) → eq x (wkv x y) ≡ diff x y
substDiff3 vz y = refl
substDiff3 (vs x) vz = refl
substDiff3 (vs x) (vs y) = substDiff2 x y (substDiff3 x y)


-- Changing the context in which a variable is typed

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → _∋_ Γ σ → _∋_ Δ σ
! refl >₀ v = v


-- Commutation between var constructors and !_>₀_

!vz : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → ! cong (λ Θ → Θ , σ) p >₀ vz ≡ vz
!vz refl = refl


!vs : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (x : _∋_ Γ τ) → ! cong (λ Θ → Θ , σ) p >₀ (vs x) ≡ vs (! p >₀ x)
!vs refl _ = refl


-- Another commutation

!! : ∀ {Γ Δ σ} → (x : _∋_ Γ σ) → (y : _∋_ Δ σ) → (p : Γ ≡ Δ) → x ≡ ! sym p >₀ y → y ≡ ! p >₀ x
!! x .x refl refl = refl


-- Changing the proof

!p : ∀ {Γ Δ σ} → (v : _∋_ Γ σ) → (p q : Γ ≡ Δ) → p ≡ q → ! p >₀ v ≡ ! q >₀ v
!p v p .p refl = refl


-- Changing the context in which a term is typed
!_>₁_ : ∀ {Γ Δ σ} → Γ ≡ Δ → _⊢_ Γ σ → _⊢_ Δ σ
! refl >₁ t = t


-- Commutation between term constructors and !_>₁_

!var : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (v : _∋_ Γ σ) → ! p >₁ var v ≡ var (! p >₀ v)
!var refl _ = refl


!Λ : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t : _⊢_ (Γ , σ) τ) → ! p >₁ Λ t ≡ Λ (! cong (λ Θ → Θ , σ) p >₁ t)
!Λ refl _ = refl


!_·_ : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t₁ : _⊢_ Γ (σ ⇒ τ)) → (t₂ : _⊢_ Γ σ) → ! p >₁ _·_ t₁ t₂ ≡ _·_ (! p >₁ t₁) (! p >₁ t₂)
!_·_ refl _ _ = refl


-- Commutation between wkTm and !_>₁_

!wkTm : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : _⊢_ Γ τ) → ! cong (λ Θ → Θ , σ) p >₁ wkTm vz u ≡ wkTm vz (! p >₁ u)
!wkTm refl _ = refl


-- Changing term inside !_>₁_

!≡₁ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : _⊢_ Γ σ} → t₁ ≡ t₂ → ! p >₁ t₁ ≡ ! p >₁ t₂
!≡₁ _ refl = refl


-- Injectivity of vs and wkv

tyInj-left : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → a ≡ b
tyInj-left refl = refl 

tyInj-right : ∀ {a b c d} → a ⇒ c ≡ b ⇒ d → c ≡ d
tyInj-right refl = refl 

vsInj : ∀ {τ Γ σ} → (i j : _∋_ Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj i .i refl = refl


wkvInj : ∀ {Γ σ τ} → (k : _∋_ Γ σ) → (i j : _∋_ (Γ - k) τ) → wkv k i ≡ wkv k j → i ≡ j
wkvInj vz vz vz p = refl
wkvInj vz vz (vs j) ()
wkvInj vz (vs i) vz ()
wkvInj vz (vs i) (vs j) p = vsInj (vs i) (vs j) p
wkvInj (vs k) vz vz p = refl
wkvInj (vs k) vz (vs j) ()
wkvInj (vs k) (vs i) vz ()
wkvInj (vs k) (vs i) (vs j) p = cong vs (wkvInj k i j (vsInj (wkv k i) (wkv k j) p))


-- Basic lemma

reflExtConSym : ∀ {Γ Δ : Con} → (σ : Ty) → (p : Γ ≡ Δ) → sym {_} {Con} (cong (λ Θ → Θ , σ) p) ≡ cong (λ Θ → Θ , σ) (sym p)
reflExtConSym _ refl = refl


vsWkvEq : ∀ {Γ σ τ} → (z x : _∋_ (Γ , τ) σ) → vs z ≡ wkv (vs vz) x → z ≡ x
vsWkvEq z vz ()
vsWkvEq z (vs x) p = vsInj z (vs x) p

rem : ∀ {Γ σ τ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> _∋_ (Γ - (wkv x y)) σ
rem vz _ = vz
rem (vs x) vz = x
rem (vs x) (vs y) = vs (rem x y)


-- Lemmas about rem

conExc : ∀ {Γ σ τ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> (Γ - x) - y ≡ (Γ - (wkv x y)) - (rem x y)
conExc vz y = refl
conExc (vs x) vz = refl
conExc (vs {σ} x) (vs y) = cong (λ Θ → Θ , σ) (conExc x y)


wkRem : ∀ {Γ σ τ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> wkv (wkv x y) (rem x y) ≡ x
wkRem vz _ = refl
wkRem (vs _) vz = refl
wkRem (vs x) (vs y) = cong vs (wkRem x y)


wkvExc : ∀ {ρ Γ σ τ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> (v : _∋_ ((Γ - x) - y) ρ) -> wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ wkv x (wkv y v)
wkvExc vz _ _ = refl
wkvExc (vs x) vz _ = refl
wkvExc (vs x) (vs y) vz =  cong (λ v → wkv (vs (wkv x y)) (wkv (vs (rem x y)) v)) (!vz (conExc x y))
wkvExc (vs x) (vs y) (vs v) = begin
  _ ≡⟨ cong (λ z → wkv (vs (wkv x y)) (wkv (vs (rem x y)) z)) (!vs (conExc x y) v) ⟩
  _ ≡⟨ cong vs (wkvExc x y v) ⟩
  _ ∎


wkTmExc : ∀ {Γ σ τ ρ} -> (x : _∋_ Γ σ) -> (y : _∋_ (Γ - x) τ) -> (t : _⊢_ ((Γ - x) - y) ρ) -> wkTm (wkv x y) (wkTm (rem x y) (! conExc x y >₁ t)) ≡ wkTm x (wkTm y t)
wkTmExc x y (var v) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!var (conExc x y) v) ⟩
  _ ≡⟨ cong var (wkvExc x y v) ⟩
  _ ∎
wkTmExc x y (Λ t) = begin
  _ ≡⟨ cong (λ u → wkTm (wkv x y) (wkTm (rem x y) u)) (!Λ (conExc x y) t) ⟩
  _ ≡⟨ cong Λ (wkTmExc (vs x) (vs y) t) ⟩
  _ ∎
wkTmExc x y (_·_ t₁ t₂) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!_·_ (conExc x y) t₁ t₂) ⟩
  _ ≡⟨ cong₂ _·_ (wkTmExc x y t₁) (wkTmExc x y t₂) ⟩
  _ ∎

wkvSubstExtAux1 : ∀ {Γ σ τ} -> (y : _∋_ Γ σ) -> (v : _∋_ (Γ - y) τ) -> (u : _⊢_ ((Γ - y) - v) τ) -> eq (wkv y v) (wkv y v) ≡ same -> wkTm (rem y v) (! conExc y v >₁ u) ≡ substVar (wkv y v) (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux1 y v u p with eq (wkv y v) (wkv y v)
wkvSubstExtAux1 y v u refl | .same = refl


wkvSubstExtAux2 : ∀ {Γ σ τ ρ} -> (y : _∋_ Γ σ) -> (v : _∋_ (Γ - y) ρ) -> (z : _∋_ ((Γ - y) - v) τ) -> (u : _⊢_ ((Γ - y) - v) ρ) -> eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ≡ diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)) -> wkTm (rem y v) (! conExc y v >₁ var z) ≡ substVar (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
  (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux2 y v z u p with eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
wkvSubstExtAux2 y v z u refl
  | .(diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) = (cong (wkTm (rem y v)) (!var (conExc y v) z))


wkvSubstExt : ∀ {Γ σ τ ρ} -> (y : _∋_ Γ σ) -> (v : _∋_ (Γ - y) τ) -> (x : _∋_ (Γ - y) ρ) -> (u : _⊢_ ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (substVar v x u)) ≡ substVar (wkv y v) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkvSubstExt y v x u with eq x v
wkvSubstExt y v .v u | same = wkvSubstExtAux1 y v u (substSame3 (wkv y v))
wkvSubstExt y .(wkv v z) .v u | diff v z = begin
  _ ≡⟨ wkvSubstExtAux2 y v z u (substDiff3 (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ⟩
  _ ≡⟨ cong (λ a → substVar a (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))) (wkvExc y v z) ⟩
  _ ∎


wkTmSubstExc : ∀ {Γ σ τ ρ} -> (y : _∋_ Γ σ) -> (t : _⊢_ (Γ - y) τ) -> (x : _∋_ (Γ - y) ρ) -> (u : _⊢_ ((Γ - y) - x) ρ) -> wkTm (rem y x) (! conExc y x >₁ (subst t x u)) ≡ subst (wkTm y t) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTmSubstExc y (var v) x u = wkvSubstExt y v x u
wkTmSubstExc y (Λ t) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!Λ (conExc y x) (subst t (vs x) (wkTm vz u))) ⟩
  _ ≡⟨ cong Λ (wkTmSubstExc (vs y) t (vs x) (wkTm vz u)) ⟩
  _ ≡⟨ cong (λ n → Λ (subst (wkTm (vs y) t) (vs (wkv y x)) (wkTm (vs (rem y x)) n))) (!wkTm (conExc y x) u) ⟩
  _ ≡⟨ cong (λ n → Λ (subst (wkTm (vs y) t) (vs (wkv y x)) n)) (wkTmExc vz (rem y x) (! conExc y x >₁ u)) ⟩
  _ ∎
wkTmSubstExc y (_·_ t₁ t₂) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!_·_ (conExc y x) (subst t₁ x u) (subst t₂ x u)) ⟩
  _ ≡⟨ cong₂ _·_ (wkTmSubstExc y t₁ x u) (wkTmSubstExc y t₂ x u) ⟩
  _ ∎

weakSubstAux : ∀ {Γ σ τ} -> (x : _∋_ Γ τ) -> (v : _∋_ (Γ - x) σ) -> (u : _⊢_ (Γ - x) τ) -> eq x (wkv x v) ≡ diff x v -> substVar (wkv x v) x u ≡ var v
weakSubstAux x v u p with eq x (wkv x v)
weakSubstAux x v u refl | .(diff x v) = refl


weakSubst : ∀ {Γ σ τ} -> (x : _∋_ Γ τ) -> (t : _⊢_ (Γ - x) σ) -> (u : _⊢_ (Γ - x) τ) -> subst (wkTm x t) x u ≡ t
weakSubst x (var v) u = weakSubstAux x v u (substDiff3 x v)
weakSubst x (Λ t) u = cong Λ (weakSubst (vs x) t (wkTm vz u))
weakSubst x (_·_ t₁ t₂) u = cong₂ _·_ (weakSubst x t₁ u) (weakSubst x t₂ u)


-- Commutation lemmas between substVar and rem, wkv

substVarCommAux2 : ∀ {Γ σ τ} -> (x : _∋_ Γ σ) -> (u₁ : _⊢_ (Γ - x) σ) -> (y : _∋_ (Γ - x) τ) -> (u₂ : _⊢_ ((Γ - x) - y) τ) -> eq (rem x y) (rem x y) ≡ same -> ! conExc x y >₁ subst u₁ y u₂ ≡ substVar (rem x y) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux2 x u₁ y u₂ p with eq (rem x y) (rem x y)
substVarCommAux2 x u₁ y u₂ refl | .same = refl


substVarCommAux1 : ∀ {Γ σ τ} -> (x : _∋_ Γ σ) -> (u₁ : _⊢_ (Γ - x) σ) -> (y : _∋_ (Γ - x) τ) -> (u₂ : _⊢_ ((Γ - x) - y) τ) -> eq (wkv x y) (wkv (wkv x y) (rem x y)) ≡ diff (wkv x y) (rem x y) -> ! conExc x y >₁ subst u₁ y u₂ ≡ subst (substVar (wkv (wkv x y) (rem x y)) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux1 x u₁ y u₂ p with eq (wkv x y) (wkv (wkv x y) (rem x y))
substVarCommAux1 x u₁ y u₂ refl | .(diff (wkv x y) (rem x y)) = substVarCommAux2 x u₁ y u₂ (substSame3 (rem x y))


substVarCommAux4 : ∀ {Γ σ τ} -> (x : _∋_ Γ τ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) σ) -> (u₂ : _⊢_ ((Γ - x) - y) σ) -> eq (wkv x y) (wkv x y) ≡ same -> ! conExc x y >₁ u₂ ≡ subst (substVar (wkv x y) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux4 x u₁ y u₂ p with eq (wkv x y) (wkv x y)
substVarCommAux4 x u₁ y u₂ refl | .same = sym (weakSubst (rem x y) (! conExc x y >₁ u₂) (! conExc x y >₁ subst u₁ y u₂))


substVarCommAux6 : ∀ {Γ σ τ ρ} -> (x : _∋_ Γ τ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) ρ) -> (u₂ : _⊢_ ((Γ - x) - y) ρ) -> (v : _∋_ ((Γ - x) - y) σ) -> eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ diff (rem x y) (! conExc x y >₀ v) -> ! conExc x y >₁ var v ≡ substVar (wkv (rem x y) (! conExc x y >₀ v)) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux6 x u₁ y u₂ v p with  eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v))
substVarCommAux6 x u₁ y u₂ v refl | .(diff (rem x y) (! conExc x y >₀ v)) = !var (conExc x y) v


substVarCommAux5 : ∀ {Γ σ τ ρ} -> (x : _∋_ Γ τ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) ρ) -> (u₂ : _⊢_ ((Γ - x) - y) ρ) -> (v : _∋_ ((Γ - x) - y) σ) -> eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ≡ diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) -> ! conExc x y >₁ var v ≡ subst (substVar (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux5 x u₁ y u₂ v p with eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)))
substVarCommAux5 x u₁ y u₂ v refl | .(diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) = substVarCommAux6 x u₁ y u₂ v
                                                                                                (substDiff3 (rem x y) (! conExc x y >₀ v))


substVarCommAux3 : ∀ {Γ σ τ ρ} -> (x : _∋_ Γ τ) -> (v : _∋_ (Γ - x) σ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) ρ) -> (u₂ : _⊢_ ((Γ - x) - y) ρ) -> ! conExc x y >₁ (substVar v y u₂) ≡ subst (substVar (wkv x v) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarCommAux3 x v u₁ y u₂ with eq y v
substVarCommAux3 x y u₁ .y u₂ | same = substVarCommAux4 x u₁ y u₂ (substSame3 (wkv x y))
substVarCommAux3 x .(wkv y v) u₁ .y u₂ | diff y v = begin
  _ ≡⟨ substVarCommAux5 x u₁ y u₂ v (substDiff3 (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ⟩
  _ ≡⟨ cong (λ z → subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)) (wkvExc x y v) ⟩
  _ ∎


substVarComm : ∀ {Γ σ τ ρ} -> (v : _∋_ Γ σ) -> (x : _∋_ Γ τ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) ρ) -> (u₂ : _⊢_ ((Γ - x) - y) ρ) -> ! conExc x y >₁ subst (substVar v x u₁) y u₂ ≡ subst (substVar v (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substVarComm v x u₁ y u₂ with eq x v
substVarComm x .x u₁ y u₂ | same = begin
  _ ≡⟨ substVarCommAux1 x u₁ y u₂ (substDiff3 (wkv x y) (rem x y)) ⟩
  _ ≡⟨ cong (λ z → subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)) (wkRem x y) ⟩
  _ ∎
substVarComm .(wkv x v) .x u₁ y u₂ | diff x v = substVarCommAux3 x v u₁ y u₂


substComm : ∀ {σ Γ τ ρ} -> (t : _⊢_ Γ σ) -> (x : _∋_ Γ τ) -> (u₁ : _⊢_ (Γ - x) τ) -> (y : _∋_ (Γ - x) ρ) -> (u₂ : _⊢_ ((Γ - x) - y) ρ) -> ! conExc x y >₁ subst (subst t x u₁) y u₂ ≡ subst (subst t (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ subst u₁ y u₂)
substComm (var v) x u₁ y u₂ = substVarComm v x u₁ y u₂
substComm {σ ⇒ _} (Λ t) x u₁ y u₂ = begin
  _ ≡⟨ !Λ (conExc x y) (subst (subst t (vs x) (wkTm vz u₁)) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong Λ (substComm t (vs x) (wkTm vz u₁) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm (vs (rem x y)) u)) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (!wkTm (conExc x y) u₂) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) u) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (wkTmExc vz (rem x y) (! conExc x y >₁ u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!≡₁ (cong (λ Θ → Θ , σ) (conExc x y)) (sym (wkTmSubstExc vz u₁ y u₂))) ⟩
  _ ≡⟨ cong (λ u → Λ (subst (subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!wkTm (conExc x y) (subst u₁ y u₂)) ⟩
  _ ∎
substComm (_·_ t₁ t₂) x u₁ y u₂ = begin
  _ ≡⟨ !_·_ (conExc x y) (subst (subst t₁ x u₁) y u₂) (subst (subst t₂ x u₁) y u₂) ⟩
  _ ≡⟨ cong₂ _·_ (substComm t₁ x u₁ y u₂) (substComm t₂ x u₁ y u₂) ⟩
  _ ∎


\end{code}
%endif