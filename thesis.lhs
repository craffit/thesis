%-------------------------------------------------------------------------------

\documentclass[11pt,twoside,a4paper]{scrreprt}

%include agda.fmt
%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include thesis.fmt
%include colorcode.fmt

%-------------------------------------------------------------------------------

% For natural deduction
\usepackage{bussproofs}
\usepackage{rotating}

\usepackage{amsmath}
% Use this arrow from amsmath before it is replaced by another package.
\let\rwarrow\rightsquigarrow

\usepackage{amsfonts}

% Use Times Roman as math font
\usepackage{mathptmx}

% Times-like fonts for math (e.g. \Coloneqq)
\usepackage{txfonts}

\usepackage{verbatim}
\usepackage{xcolor}

\usepackage{hyperref}
\usepackage{url}

% For \inferrule
\usepackage{mathpartir}

% Theorems
\usepackage{ntheorem}
\theoremstyle{break}
\theorembodyfont{\normalfont}
\newtheorem{defn}{Definition}
\newtheorem{thrm}{Theorem}
\newtheorem{law}{Law}

\begin{document}

\tableofcontents

\chapter{Introduction}
%include introduction.lhs

\chapter{TTS System}
%include tts.lhs

\chapter{Tools of the Trade}
%include tools.lhs

\chapter{Proof}
%include proof.lhs

\chapter{Mechanical Proof}
%include proof.lagda

\chapter{Conclusion}
%include conclusion.lhs

%-------------------------------------------------------------------------------
\bibliographystyle{abbrvnat}
\bibliography{thesis}

\end{document}

