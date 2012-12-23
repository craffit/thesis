%if False
\begin{code}
module STLC.Context.Base where

open import STLC.Types public

infixl 5 _,_  

\end{code}
%endif
\begin{code}

data Con : Set where
  ε    : Con
  _,_  : Con → Ty → Con

\end{code}