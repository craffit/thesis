\begin{code}

open import STLC

module TTS.Relation  (A : ℕ) (R : Ty) (rep : ε ⊢ C A ⇒ R) where

import TTS.Relation.Base
open TTS.Relation.Base A R rep public
import TTS.Relation.Properties
open TTS.Relation.Properties A R rep public


\end{code}