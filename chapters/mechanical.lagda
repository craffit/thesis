%include ../formatting/agda.fmt

This chapter 

% poplMARK? 
\section{STLC object language}

%include ../proof/STLC/Base.lagda

%include ../proof/STLC/Up.lagda

%include ../proof/STLC/SSubst.lagda

\subsection{Equality}
%include ../proof/STLC/Equality.lagda

\section{Tools for equational reasoning}
Proofs in Agda can become big and unwieldy, even for a small domain such as STLC. During the development of this proof a few tricks (tactics) were employed which will be demonstrated here.


\subsection{Structuring proofs}
%include ../proof/STLC/Syntax.lagda

\subsection{Beta-equivalence tactic}
%include ../proof/STLC/Eval.lagda

\section{Typing functor}
%include ../proof/TTS/Functor.lagda

\section{Formalization}
%include ../proof/TTS/Context.lagda
%include ../proof/TTS.lagda

\section{Proof}

