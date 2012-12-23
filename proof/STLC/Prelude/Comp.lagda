%if False
\begin{code}
module STLC.Prelude.Comp where

open import STLC.Term
open import STLC.Prelude.Base

import Relation.Binary.EqReasoning
open import Util.PropositionalEquality

eval-comp  : ∀ {a b c} → (g : ε ⊢ b ⇒ c) → (f : ε ⊢ a ⇒ b) → (a : ε ⊢ a) 
           → ((g ∘ f) · a) βη-≡ (g · (f · a))
eval-comp f g a = 
  let open Relation.Binary.EqReasoning βηsetoid
          renaming (_≈⟨_⟩_ to _⟷⟨_⟩_ ; _≡⟨_⟩_ to _β⟨_⟩_)
  in  begin
      _ ⟷⟨ {!!} ⟩
      _ ⟷⟨ {!!} ⟩
      _ ⟷⟨ {!!} ⟩
      _ ∎

\end{code}
%endif