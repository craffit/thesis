%-------------------------------------------------------------------------------

\documentclass[11pt,twoside,a4paper]{scrreprt}

%include agda.fmt
%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include thesis.fmt
%include colorcode.fmt

%include formatting/general.fmt

%-------------------------------------------------------------------------------

% For natural deduction
\usepackage{bussproofs}
\usepackage{rotating}

% For encoding
\usepackage[utf8x]{inputenc}

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

\usepackage{float}

\usepackage{overlay}

\usepackage{rotating}
% Theorems
\usepackage{ntheorem}
\theoremstyle{break}
\theorembodyfont{\normalfont}
\newtheorem{defn}{Definition}
\newtheorem{prop}{Property}
\newtheorem{thrm}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{proof}{Proof}
\newtheorem{law}{Law}

\begin{document}

\tableofcontents

\chapter{Introduction}
%include chapters/introduction.lhs

\chapter{TTS System}
%include chapters/tts.lhs

\chapter{Proof}
%include chapters/proof.lhs

\chapter{Mechanical Proof}
%%include chapters/mechanical.lagda

\chapter{Extensions to the TTS system}
%include chapters/ttse.lhs

\chapter{Conclusion}
%include chapters/conclusion.lhs

%-------------------------------------------------------------------------------
\nocite{*}
\bibliographystyle{alpha}
\bibliography{thesis}

\end{document}

