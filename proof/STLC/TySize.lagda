\begin{code}
module STLC.TySize where

open import STLC.Base
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum

open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

τsize : Ty → ℕ
τsize ○ = suc zero
τsize (y ⇒ y') = τsize y + τsize y'

≡-to-≤ : ∀ {n m} → n ≡ m → n ≤ m
≡-to-≤ {zero} {zero} p = z≤n
≡-to-≤ {suc n} {zero} ()
≡-to-≤ {zero} {suc n'} ()
≡-to-≤ {suc .n'} {suc n'} refl = s≤s (≡-to-≤ {n'} {n'} refl)

≤+ : ∀ {a b n m} → a ≤ b → n ≤ m → a + n ≤ b + m
≤+ {zero} {b} z≤n p2 = ≤-steps b p2
≤+ (s≤s m≤n) p2 = s≤s (≤+ m≤n p2)

τsize-1 : {t : Ty} → 1 ≤ τsize t
τsize-1 {○} = s≤s z≤n
τsize-1 {y ⇒ y'} = ≤-steps (τsize y) (τsize-1 {y'})

τs-eq : ∀ {τ σ} → τ ≡ σ → τsize τ ≡ τsize σ
τs-eq {○} {○} p = refl
τs-eq {○} {y ⇒ y'} ()
τs-eq {y ⇒ y'} {○} ()
τs-eq {y ⇒ y'} {y0 ⇒ y1} p = cong₂ _+_ (τs-eq (tyInj-left p)) (τs-eq (tyInj-right p))

τs-neq : ∀ {τ σ} → (τsize τ ≡ τsize σ → ⊥) → τ ≡ σ → ⊥
τs-neq f p = f (τs-eq p)
\end{code}
