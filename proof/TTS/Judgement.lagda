\begin{code}

open import STLC public
open import TTS.Rules.Base

module TTS.Judgement
       (A : ℕ) (R : Ty) 
       (rep : ε ⊢ C A ⇒ R) (abs : ε ⊢ R ⇒ C A) 
       (rules : Rules A R)
         where

import TTS.Judgement.Base
open TTS.Judgement.Base A R rep abs rules public
import TTS.Judgement.Properties
open TTS.Judgement.Properties A R rep abs rules public
\end{code}
