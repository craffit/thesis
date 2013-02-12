%-------------------------------------------------------------------------------

\documentclass[11pt,twoside,a4paper]{scrreprt}

%include agda.fmt
%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include colorcode.fmt

%include formatting/general.fmt
%include formatting/haskell.fmt

%-------------------------------------------------------------------------------
%Contains HACKs supprressing warnings for scrreprrt
\usepackage{scrhack}

% For natural deduction
\usepackage{bussproofs}
\usepackage[figuresright]{rotating}

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

\usepackage{url}

% For \inferrule
\usepackage{mathpartir}

\usepackage{float}

\usepackage{overlay}

% Theorems
\usepackage{ntheorem}

\usepackage{hyperref}
\usepackage{enumitem}
\usepackage{nameref}

\usepackage{relsize}

%% Command for labelled items

\makeatletter
\def\namedlabel#1#2{\begingroup
   \def\@@currentlabel{#2}%
   \phantomsection\label{#1}\endgroup
}
\makeatother

\theoremstyle{break}
\theorembodyfont{\normalfont}
\newtheorem{defn}{Definition}
\newtheorem{prop}{Property}
\newtheorem{thrm}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{proof}{Proof}
\newtheorem{corollary}{Corollary}
\newtheorem{law}{Law}

\title{A Type-Changing, Equivalence-Preserving Program Transformation System}
\date{February 11, 2013}
\author{Bram Schuur \thanks{Msc. Thesis under supervision of Johan Jeuring and Sean Leather}}

\hfuzz=15.002pt

\begin{document}

\maketitle

\begin{abstract}
%include chapters/abstract.lhs
\end{abstract}

\tableofcontents

\chapter{Introduction}
\label{chap:introduciton}
%include chapters/introduction.lhs

\chapter{Type and Transform Systems}
\label{chap:tts}
This chapter introduces the core concepts of type and transform systems. The first section gives two motivating examples of type-changing program transformations which will be used throughout this work.
\section{Motivating Examples}
\label{sec:examples}
%include chapters/examples.lhs

\section{Core Transformation System}
\label{sec:tts}
%include chapters/tts.lhs

\chapter{\texorpdfstring{|(TTS(stlc))|}{TTS stlc}  Preserves the Transformation Properties}
\label{chap:proof}
%include chapters/proof.lhs

\chapter{Mechanical Proof of the Transformation Properties}
\label{chap:mechanical}
%include chapters/mechanical.lagda

\chapter{Extensions to the TTS system}
\label{chap:extensions}
%include chapters/ttse.lhs

\chapter{Future work}
\label{chap:future}
%include chapters/future.lhs

\chapter{Conclusion}
\label{chap:conclusion}
%include chapters/conclusion.lhs

%-------------------------------------------------------------------------------
\nocite{*}
\bibliography{thesis}
\bibliographystyle{alpha}


\end{document}

