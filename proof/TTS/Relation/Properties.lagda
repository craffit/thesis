%if False
\begin{code}

open import STLC

module TTS.Relation.Properties  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

import TTS.Relation.Base
open TTS.Relation.Base A R rep

open import TTS.Functor.Base
open import TTS.Context.Base
import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

\end{code}
%endif

Before proving the Fundamental Lemma we first establish the $\beta\eta$-closure and crossing lemma's over the logical relation. Because the type of the logical relation depends on the functor, there is no choice but to prove properties about the logical relation by induction on the typing functor. 

\begin{code}
rel-βη  : ∀ {φ Φ} {e e' : ⟦ φ ⟧φ C A ⊢ ⟦ Φ ⟧Φ C A} {f f' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R}
        → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) → e βη-≡ e' → f βη-≡ f' 
        → rel {φ} {Φ} e f s s' → rel {φ} {Φ} e' f' s s'
rel-βη {φ} {Id}        s s' eq1 eq2 r  =   (□ %· %close s (bsym eq1)) 
                                       ⟷  r 
                                       ⟷  %close s' eq2
rel-βη {φ} {C n}       s s' eq1 eq2 r  =   %close s (bsym eq1) 
                                       ⟷  r 
                                       ⟷  %close s' eq2
rel-βη {φ} {Φ₁ ⟶ Φ₂}   s s' eq1 eq2 r = 
      λ a a' ra →  rel-βη {φ} {Φ₂} s s' (eq1 %· □) (eq2 %· □) (r a a' ra)
\end{code}

The $\beta\eta$ closure proof is another good example of the Curry-Howard correspondence in action. In the proof of Chapter~\ref{chap:proof} we used sequences of implication to show the case for function space. In the Curry-Howard correspondence implication elimination becomes function application.

For the Crossing Lemma we just show the types, which give an exact formal representation of the lemma. The logical equivalence of the crossing lemma is proven by mutual induction on the two directions of the implication, in Agda we can model this by using a mutual block. Agda's termination checker will tell whether we have cyclic reasoning or not: if the construction of the proof term terminates, we have no cyclic reasoning, if it is proven using infinite recursion the reasoning was cyclic.

\begin{code}
mutual
  cross-left   : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧φ C A , ⟦ Φ' ⟧Φ C A ⊢ ⟦ Φ ⟧Φ C A) 
               → (e' :  ⟦ φ ⟧φ R , ⟦ Φ' ⟧Φ R ⊢ ⟦ Φ ⟧Φ R) 
               → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) 
               → (a : ⟦ φ ⟧φ C A ⊢ ⟦ Φ' ⟧Φ C A) → (a' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ' ⟧Φ R)
               → rel {φ} {Φ} (e / sub vz a) (e' / sub vz a') s s'
               → rel {φ , Φ'} {Φ} e e' (cls s a) (cls s' a') 

  cross-right  : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧φ C A , ⟦ Φ' ⟧Φ C A ⊢ ⟦ Φ ⟧Φ C A) 
               → (e' : ⟦ φ ⟧φ R , ⟦ Φ' ⟧Φ R ⊢ ⟦ Φ ⟧Φ R) 
               → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) 
               → (a : ⟦ φ ⟧φ C A ⊢ ⟦ Φ' ⟧Φ C A) → (a' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ' ⟧Φ R)
               → rel {φ , Φ'} {Φ} e e' (cls s a) (cls s' a') 
               → rel {φ} {Φ} (e / sub vz a) (e' / sub vz a') s s'
\end{code}

The entire proof for this lemma can be found in the sources.

%if False
\begin{code}
  rel-weak     : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧φ C A  ⊢ ⟦ Φ ⟧Φ C A) 
               → (e' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R) 
               → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) 
               → (a : ⟦ φ ⟧φ C A ⊢ ⟦ Φ' ⟧Φ C A) → (a' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ' ⟧Φ R)
               → rel {φ} {Φ} e e' s s'
               → rel {φ , Φ'} {Φ} (wkTm vz e) (wkTm vz e') (cls s a) (cls s' a')

  cross-left {φ} {Id} e e' s s' a a' r =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ □ %· e -%/ ss (=>≡ (sym (I/=> (↓-=> s)))) □ ⟩
     _ ⟷⟨ □ %· %≡ split-/ e (ss I a) (↓-=> s) ⟩
     _ ⟷⟨ r ⟩
     _ ⟷⟨ %≡ merge-/ e' (ss I a') (↓-=> s') ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (I/=> (↓-=> s'))) □ ⟩
     _ ∎
  cross-left {φ} {C n} e e' s s' a a' r =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ e -%/ ss (=>≡ (sym (I/=> (↓-=> s)))) □ ⟩
     _ ⟷⟨ %≡ split-/ e (ss I a) (↓-=> s) ⟩
     _ ⟷⟨ r ⟩
     _ ⟷⟨ %≡ merge-/ e' (ss I a') (↓-=> s') ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (I/=> (↓-=> s'))) □ ⟩
     _ ∎
  cross-left {φ} {Φ₁ ⟶ Φ₂} {Φ'} e e' s s' a a'  re = λ a0 a1 r → 
     cross-left {φ} {Φ₂} {Φ'} (e · a0) (e' · a1) s s' a a' 
    (re (a0 / ss I a) (a1 / ss I a') 
    (cross-right {φ} {Φ₁} {Φ'} a0 a1 s s' a a' r))

  rel-weak {φ} {Φ} {Φ'} e e' s s' a a' re = cross-left {φ} {Φ} {Φ'} (wkTm vz e) (wkTm vz e') s s' a a' (≡rel {φ} {Φ} (sym (wkTm/sub vz e a)) (sym (wkTm/sub vz e' a')) refl refl re)


  cross-right {φ} {Id} e e' s s' a a' re =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ □ %· %≡ merge-/ e (ss I a) (↓-=> s) ⟩
     _ ⟷⟨ □ %· e -%/ ss (=>≡ (I/=> (↓-=> s))) □ ⟩
     _ ⟷⟨ re ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (sym (I/=> (↓-=> s')))) □ ⟩
     _ ⟷⟨ %≡ split-/ e' (ss I a') (↓-=> s') ⟩
     _ ∎
  cross-right {φ} {C n} e e' s s' a a' re =
    let open Relation.Binary.EqReasoning βηsetoid
           renaming (_≈⟨_⟩_ to _⟷⟨_⟩_)
    in begin
     _ ⟷⟨ %≡ merge-/ e (ss I a) (↓-=> s) ⟩
     _ ⟷⟨ e -%/ ss (=>≡ (I/=> (↓-=> s))) □ ⟩
     _ ⟷⟨ re ⟩
     _ ⟷⟨ e' -%/ ss (=>≡ (sym (I/=> (↓-=> s')))) □ ⟩
     _ ⟷⟨ %≡ split-/ e' (ss I a') (↓-=> s') ⟩
     _ ∎
  cross-right {φ} {Φ₁ ⟶ Φ₂} {Φ'} e e' s s' a a' re = λ a0 a1 r → 
    ≡rel {φ} {Φ₂} (refl ≡· wkTm/sub vz a0 a) (refl ≡· wkTm/sub vz a1 a') refl refl
      (cross-right {φ} {Φ₂} {Φ'} _ _ s s' a a' 
      (re (wkTm vz a0) (wkTm vz a1) 
      (rel-weak {φ} {Φ₁} {Φ'} a0 a1 s s' a a' r)))

rel-weak' : ∀ {φ Φ Φ'} → (e : ⟦ φ ⟧φ C A  ⊢ ⟦ Φ ⟧Φ C A) 
         → (e' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ ⟧Φ R) 
         → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) 
         → (a : ⟦ φ ⟧φ C A ⊢ ⟦ Φ' ⟧Φ C A) → (a' :  ⟦ φ ⟧φ R ⊢ ⟦ Φ' ⟧Φ R)
         → rel {φ , Φ'} {Φ} (wkTm vz e) (wkTm vz e') (cls s a) (cls s' a')
         → rel {φ} {Φ} e e' s s'
rel-weak' {φ} {Φ} {Φ'} e e' s s' a a' r = 
  ≡rel {φ} {Φ} (wkTm/sub vz e a) (wkTm/sub vz e' a') refl refl
 (cross-right {φ} {Φ} {Φ'} (wkTm vz e) (wkTm vz e') s s' a a' r)

rel-up : ∀ {φ Φ} → (e : ε ⊢ ⟦ Φ ⟧Φ C A) → (e' : ε ⊢ ⟦ Φ ⟧Φ R) 
       → (s : ⟦ φ ⟧φ C A ↓) → (s' : ⟦ φ ⟧φ R ↓) 
       → rel {ε} {Φ} e e' ε ε
       → rel {φ} {Φ} (up e) (up e') s s'
rel-up {ε} {Φ} e e' ε ε r = ≡rel {ε} {Φ} (sym (/I e)) (sym (/I e')) refl refl r
rel-up {φ , Φ'} {Φ} e e' (cls y y') (cls y0 y1) r = cross-left {φ} {Φ} _ _ y y0 y' y1 (≡rel {φ} {Φ} (split-/ e sz _) (split-/ e' sz _) refl refl (rel-up {φ} {Φ} e e' y y0 r))
\end{code}
%endif