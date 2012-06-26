%-------------------------------------------------------------------------------

\documentclass[11pt,twoside,a4paper,openright]{scrreprt}

%include polycode.fmt

%-------------------------------------------------------------------------------

\usepackage{amsmath}
% Use this arrow from amsmath before it is replaced by another package.
\let\rwarrow\rightsquigarrow

\usepackage{amsfonts}

% Use Times Roman as math font
\usepackage{mathptmx}

% Times-like fonts for math (e.g. \Coloneqq)
\usepackage{txfonts}

% MnSymbol does not play well with mathptmx
%\usepackage{MnSymbol}

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

\newcommand{\Johan}[1]{\{{\bf Johan:} #1\}}
\newcommand{\Bram}[1]{\{{\bf Bram:} #1\}}
%-------------------------------------------------------------------------------

%format prime    = "^{\prime}"
%format (vec(x)) = "\overline{" x "}"

%format forall  = "{\forall}"
%format forall' = "{\forall}"
%format `ret`  = "\vartriangleleft "
%format `solve` = "\vartriangleright "
%format `rw`   = "\rightsquigarrow "
%format `rwe`  = "\rightsquigarrow_{\rho} "
%format `rwera` = "\rightsquigarrow_{\alpha} "
%format .      = "."
%format `comp` = "\circ "
%format `uni`  = "\sqcap"
%format `to`   = " \mapsto "
%format `notelem` = "\notin"
%format `union` = "\cup"
%format alpha = "\alpha"

%format beta   = "\beta "
%format beta_1 = "\beta_1 "
%format beta_2 = "\beta_2 "
%format beta_2 = "\beta_2 "
%format beta_s = "\beta_s "
%format beta_a = "\beta_a "
%format beta_r = "\beta_r "
%format beta'  = beta prime

%format dimap_F = "dimap_{\Phi}"
%format dimap_FA = "dimap_{\Phi A}"
%format dimap_FR = "dimap_{\Phi R}"
%format dimap_Ff = "dimap_{\Phi f}"
%format dimap_Fa = "dimap_{\Phi a}"
%format dimap_Fr = "dimap_{\Phi r}"
%format dimap_F1 = "dimap_{\Phi 1}"
%format dimap_F2 = "dimap_{\Phi 2}"
%format dimap_F' = "dimap_{\Phi\prime}"
%format dimap_F1F2 = "dimap_{{\Phi}1\to {\Phi}2}"
%format dimap_I  = "dimap_{I}"
%format dimap_K  = "dimap_{K}"
%format dimap_Id  = "dimap_{Id}"
%format dimap_A  = "dimap_{A}"
%format dimap_T  = "dimap_{T}"
%format dimap_ty  = "dimap_{\tau}"
%format (dimap(x)) = "dimap_{" x "}"
%format mdimap_T  = "mdimap_T"

%format F       ="\Phi"
%format F_a     ="\Phi_a"
%format F_r     ="\Phi_r"
%format F_f     ="\Phi_f"
%format F_ty     ="\Phi_{\tau}"
%format F_x     ="\Phi_x"
%format F_1     ="\Phi_1"
%format F_2     ="\Phi_2"
%format F'      = F prime

%format G     ="\Gamma"
%format G_s   ="\Gamma_s "
%format G_r   ="\Gamma_r "
%format Gx    ="\Gamma^x "
%format Gx_s  ="\Gamma_s\backslash x "
%format Gx_r  ="\Gamma_r\backslash x "
%format G'    =G prime

%format C     ="\mathcal{C}"
%format C_1   ="\mathcal{C}_1 "
%format C_2   ="\mathcal{C}_2 "
%format C_3   ="\mathcal{C}_3 "
%format C_s   ="\mathcal{C}_s "
%format C_r   ="\mathcal{C}_r "
%format Cx    ="\mathcal{C}^x "
%format Cx_s  ="\mathcal{C}_s\backslash x "
%format Cx_r  ="\mathcal{C}_r\backslash x "
%format C'    =C prime

%format T_a     ="T_a"
%format T_b     ="T_b"

%format AS     ="\mathcal{A}"
%format AS_1   ="\mathcal{A}_1 "
%format AS_2   ="\mathcal{A}_2 "
%format AS_s   ="\mathcal{A}_s "
%format AS_r   ="\mathcal{A}_r "
%format ASx    ="\mathcal{A}^x "
%format ASx_s  ="\mathcal{A}_s\backslash x "
%format ASx_r  ="\mathcal{A}_r\backslash x "
%format AS'    =AS prime

%format D     ="\Delta"
%format D_s   ="\Delta_s "
%format D_r   ="\Delta_r "
%format Dx    ="\Delta^x "
%format Dx_s  ="\Delta_s\backslash x "
%format Dx_r  ="\Delta_r\backslash x "
%format D'   =D prime

%format O       ="\Omega "

%format P       ="\Theta "
%format P_s     ="\Theta_s "
%format P_r     ="\Theta_r "
%format P_1     ="\Theta_1 "
%format P_2     ="\Theta_2 "
%format P_x     ="\Theta_x "
%format Px      ="\Phi\backslash x"
%format Om      ="\Omega"
%format empty   ="\emptyset"
%format `subsetof` = "\subseteq"
%format x_s     ="x_s"
%format x_r     ="x_r"

%format <=>     ="\Leftrightarrow"
%format +->     ="\mapsto"
%format +=      ="\models"
%format +-     ="\vdash "
%format &       ="\times"
%format ==>     ="\Longrightarrow" 

%format `rwr`  = "\vdash_{rw}"
%format `pro`  = "\vdash_{pro}"
%format `tr`   = "\vdash_{tr}"
%format `sol`   = "\vdash_{sol}"
%format `mat`   = "\vdash_{mat}"
%format `app`   = "\vdash_{app}"
%format `env`   = "\vdash_{env}"
%format `rew`   = "\vdash_{rew}"
%format `ty`    = "\vdash_{ty}"

%format env     = "\rho "

%format t_a     ="t_a"
%format t_r     ="t_r"

%format <<      ="{\llbracket}"
%format >>      ="\rrbracket_"

%format </      ="{\llbracket}"
%format />      ="\rrbracket"

%format ty       ="\tau"
%format tyl      ="\vec{\tau}"
%format ty_1     ="\tau_1"
%format ty_2     ="\tau_2"
%format ty_a     ="\tau_a"
%format ty_s     ="\tau_s"
%format ty_r     ="\tau_r"
%format ty_i     ="\tau_i"
%format ty_x     ="\tau_x"
%format ty_f     ="\tau_f"

%format ty'      =ty prime
%format ty_1'    =ty_1 prime 
%format ty_2'    =ty_2 prime
%format ty_a'    =ty_a prime
%format ty_s'    =ty_s prime
%format ty_r'    =ty_r prime
%format ty_x'    =ty_x prime
%format ty_i'    =ty_i prime
%format ty_f'    =ty_f prime

%format sch       ="\sigma"
%format sch_1     ="\sigma_1"
%format sch_2     ="\sigma_2"
%format sch_a     ="\sigma_a"
%format sch_s     ="\sigma_s"
%format sch_r     ="\sigma_r"
%format sch_x     ="\sigma_x"
%format sch_f     ="\sigma_f"

%format sch'      =sch prime
%format sch_1'    =sch_1 prime 
%format sch_2'    =sch_2 prime
%format sch_a'    =sch_a prime
%format sch_s'    =sch_s prime
%format sch_r'    =sch_r prime
%format sch_x'    =sch_x prime
%format sch_f'    =sch_f prime

%format hty       ="\pi"
%format hty_1     ="\pi_1"
%format hty_2     ="\pi_2"
%format hty_a     ="\pi_a"
%format hty_s     ="\pi_s"
%format hty_r     ="\pi_r"
%format hty_x     ="\pi_x"
%format hty_f     ="\pi_f"

%format hty'      =hty prime
%format hty_1'    =hty_1 prime 
%format hty_2'    =hty_2 prime
%format hty_a'    =hty_a prime
%format hty_s'    =hty_s prime
%format hty_r'    =hty_r prime
%format hty_x'    =hty_x prime
%format hty_f'    =hty_f prime

%format sig      ="\sigma"
%format sig_a    ="\sigma_a"
%format sig_s    ="\sigma_s"
%format sig_r    ="\sigma_r"
%format sig_1    ="\sigma_1"
%format sig_2    ="\sigma_2"


%format sig'     =sig prime

%format sub     ="\theta"
%format sub_f    ="\theta_f"
%format sub_a    ="\theta_a"
%format sub_r    ="\theta_r"
%format sub_s    ="\theta_s"
%format sub_x    ="\theta_x"
%format sub_e    ="\theta_e"
%format sub_1    ="\theta_1"
%format sub_2    ="\theta_2"

%format sub'     =sub prime
%format sub_f'   =sub_f prime
%format sub_a'   =sub_a prime
%format sub_r'   =sub_r prime
%format sub_s'   =sub_s prime
%format sub_x'   =sub_x prime
%format sub_e'   =sub_e prime
%format sub_1'   =sub_1 prime
%format sub_2'   =sub_2 prime

%format sub_gf    = "\theta_{\Gamma, x : \Phi}"
%format sub_gfa   = "\theta_{\Gamma, x : \Phi_a}"
%format sub_empty = "\theta_{\emptyset} "
%format sub_G     = "\theta_{\Gamma}"
%format sub_P    ="\theta_{\Theta}"
%format sub_Ps   ="\theta_{\Theta s}"
%format sub_Pr   ="\theta_{\Theta r}"
%format sub_Px   ="\theta_{\Theta x}"
%format sub_P1   ="\theta_{\Theta 1}"
%format sub_P2   ="\theta_{\Theta 2}"
%format sub_2    ="\theta_2"

%format Sub      ="\Theta"
%format Sub_1    ="\Theta_1"
%format Sub_2    ="\Theta_2"

%format e_x       ="e_x"
%format e_x'      =e_x prime
%format e_1       ="e_1"
%format e_1'      =e_1 prime
%format e_2       ="e_2"
%format e_2'      =e_2 prime

%format al = "\alpha"
%format al_0 = "\alpha_0"
%format bet = "\beta"
%format bet' = bet prime


\begin{document}

\title{Proving semantics preserving program transformations}

\maketitle

%-------------------------------------------------------------------------------

\tableofcontents

\section{Introduction}

In this work we will present a program transformation system which allows both the types
and terms of a program to change, while maintaining the guarantee that the semantics have
not changed.

\section{Type and Transform Systems}
A type and transform system (TTS) transforms a program which, when the transformation
is successful, guarantees the following TTS properties:

\begin{itemize}
  \item The source and result program are well-typed
  \item The source and result program are semantically equivalent
\end{itemize}

At the heart of a TTS is the TTS relation. The TTS relation specifies which well-typed 
source programs can be turned into a well-typed result program, as such:

> e : ty `rw` e' : ty'

Elements of this relation are defined using inference rules, much like inference rules in normal type systems. However,
the TTS system validates and types the source and result terms simultaneously. The inference rules 
of the TTS system should also make sure that the TTS properties we defined for the system are maintained. 

For a TTS system to be of any use, it should allow the user to specify transformations rules. Because the
system still has to make sure the TTS properties are satisfied, the TTS can place restrictions on 
the transformations supplied by the user and the form of the source program. Thus the trick in 
creating a useful TTS is keeping the restrictions to a minimum while still being able to prove the TTS properties.

Thus far we have not defined what form the terms and types of the TTS system should be, nor have
we specified what the user-created transformations should look like. A TTS is a general
concept and could be defined for any terms and types as long as we can prove the desired TTS properties 
within the system we are defining.

The language for which we design the TTS is called the object language. We will now give an example 
of a simple TTS with as object language the simply typed lambda calculus.

\section{A TTS for STLC}
In this chapter we present a TTS for the simply typed lambda calculus. Although this is
a simple example, it contains all the essential elements a TTS should have. A proof
of correctness of this system can be found in Appendix A.

To recap, the terms and types of the simply typed lambda calculus are of the following form:

> e ::= x | c | e e | \x. e
> ty ::= T | ty -> ty

\subsection{The typing functor}
Because we are building a TTS we want to allow the types of terms to change. However,
allowing arbitrary type changes makes proving the TTS properties very hard. We
want to maintain control over how and where the types have changed. To this end, we
extend the normal STLC types with a `hole` (|Id|) as follows.

> F ::= Id | T | F -> F

This hole is a special construct that can be filled in with a normal type to obtain a normal 
type again, as defined by the following interpretation function:

> <<F>>ty -> ty
> <<T>>ty           = T
> <<Id>>ty          = ty
> <<F_1 -> F_2>>ty  = <<F_1>>ty -> <<F_2>>ty

Thus |F| can be applied to a type to yield a new type. We call |F| a typing functor. We can
now use this typing functor to express that we only want to change one type in the program,
by constructing the TTS judgement in the following way:

> e : <<F>>A `rw` e' : <<F>>R

This enforces that only |A|s are transformed into |R|s, the rest of the type remains the same. The types
types |A| and |R| play a special role. In the final implementation of the system the user
can manually specify which types a transformation will transform. Thus |A| and |R| are `global` in the TTS
system and we implicitly assume them to be specified. Because of this, we rewrite
the TTS judgement in a shorter form:

> e `rw` e' : F

where the properties |typeOf(e) == <<F>>A| and |typeOf(e') == <<F>>R| are left implicit.

STLC inference rules also contain a typing environment which assumes types for unbound
variables. We want to allow changes in the types of unbound variables, but we also want to
allow changing of the variables themselves to allow for rewriting. Thus we get the following
rewrite environment:

> G ::= empty | G, x `rw` x' : F

Thus we have merged both the types and the environments of the source and result program into
one, with the functor |F| accounting for the differences that may exist. With these building 
blocks in place, we and up with the following judgement for our STLC TTS system:

> G +- e `rw` e' : F

The typing functor plays a crucial part in connecting the source and result programs. Before looking
at user-supplied transformation rules, we will first introduce some theory behind functors.

\subsection{Functors}
A functor can be seen as a function on types. It takes as parameter a type and yields a 
new type based on its argument. Associated with a type level functor is a term level functor which 
lifts functions on the type parameter to functions on the functor:

> type F a                          --Functor
> fmap :: (a -> b) -> F a -> F b    --term level functor

For |fmap| to be a proper term-level functor it has to obey the functor laws:

> fmap id = id                              --Identity
> fmap g `comp` fmap f = fmap (g `comp` f)  --Composition

A list is an example of a Functor in Haskell:

> data List a = Nil | Cons a (List a)
> fmap :: (a -> b) -> List a -> List b
> fmap _ Nil         = Nil
> fmap f (Cons a l)  = Cons (f a) (fmap f l)

What makes functors special, is that an implementation for the term level function |fmap| can 
be constructed from the functor type. This is what makes functors useful for our purpose. We
can reason about the semantics of the terms by knowing the types.

For normal functors we can only construct a term-level functor when the argument type
occurs in covariant positions within the datatype. This means we can construct |fmap| for all
polynomial types (datatypes without functions), but not for all datatypes containing functions.
However, our typing functor |F| includes a function space constructor, so we will need something more powerful. 

Meijer and Hutton\cite{meijer} showed that it is possible to define functors for function types 
(exponential types) when we use |dimap|s. A |dimap| is the same as as a normal |fmap| but with an extra
function argument which can be used for occurrences of the type parameter at contra-variant
positions. The functor laws also have an extended version for |dimap|s:

> dimap_F :: (a -> b) -> (b -> a) -> F b -> F a

> dimap_F id id = id
> dimap_F g1 g2 `comp` dimap_F f1 f2 = dimap_F (f1 `comp` g1) (g2 `comp` f2)

Note how the first function is contra-variant and the second covariant in the result type. 

Based on this work, we can define how the term-level |dimap| is derived from our typing functor
using the following type-indexed function:

> dimap_F :: (a -> b) -> (b -> a) -> <<F>>b -> <<F>>a
> dimap_Id    rep abs x = abs x
> dimap_T     rep abs x = x
> dimap_F1F2  rep abs f = dimap_F2 rep abs `comp` f `comp` dimap_F1 abs rep

\subsection{F-Algebras}
An algebra is a construct consisting of a carrier type and one or more functions
on that carrier type which can abide certain laws. A special type of algebra is the F-algebra,
and algebra based on functors. An F-algebra is a tuple |(A, f)| where |A| is the carrier type and
|f| is a function of type |F A -> A| for some functor F. In other words, the function f 'folds'
something of type |F A| into something of type |A|. The dual notion of an F-algebra is a F-coalgebra,
defined as a tuple |(B, g)| where |g| is of type |B -> F B|. The unification of these two concepts is
a F-G-dialgebra, which, not surprisingly, is a tuple |(C, h)| with |h| of type |F C -> G C|.

\paragraph{Homomorphism}
Algebras alone are not of little interest to us. However, the relations that may exist among algebras
provide a strong mathematical foundation to reason about program transformations. One relation that may
exist between two algebras, is that there exists an so-called homomorphism between them. Given
two dialgebras |(A, f :: F A -> G A)| and |(R, g :: F R -> G R)| the may exist two functions 
|(rep :: A -> R, abs :: R -> A)| which make the following equality hold:

> dimap_G abs rep `comp` f == g `comp` dimap_F abs rep

In this case, rep and abs are a homomorphism for the F-G-dialgebras |(A, f)| and |(R, g)|.

\paragraph{Relating homomorphisms and functors}
As we can see from the laws, a homomorphism between F-G-dialgebras states almost the same
property as a functor. Actually, the homomorphism implies a functor for |rep| and |abs| which form
a retraction:

> dimap_G abs rep `comp` f == g `comp` dimap_F abs rep
>== { Apply dimap_G rep abs to both sides }
> dimap_G rep abs `comp` dimap_G abs rep `comp` f == dimap_G rep abs `comp` g `comp` dimap_F abs rep
>== { Functor composition }
> dimap_G (abs `comp` rep) (abs `comp` rep) f == dimap_G rep abs `comp` g `comp` dimap_F abs rep
>== { Retraction }
> dimap_G id id f == dimap_G rep abs `comp` g `comp` dimap_F abs rep
>== { Functor identity }
> f == dimap_G rep abs `comp` g `comp` dimap_F abs rep
>== { Definition functor }
> f == (dimap(F -> G)) rep abs g

\subsection{F-G-Dialgebras and functions with multiple arguments}
By the definition of F-G-Dialgebras we can see that this system does not readily support
functions with multiple arguments. Algebras only work on functions in uncurried form. To
relate functors and homomorphisms properly, we will need a way to convert between curried
and uncurried functors. We use the following definition for uncurried functors:

> P' ::= Id | T | P' * P'
> P ::= P' | P' -> P | P * P

Converting between curried and uncurried functions is done using the following functions:

> uncurry_F : F -> P
> uncurry_Id   = Id
> uncurry_T    = T
> uncurry_F->G =
>   case uncurry_G of
>     P -> P' = uncurry_F * P -> P'
>     x       = uncurry_F -> x


\subsection{Rewrite rules}
Naturally we want to allow the user to supply custom rewrite rules to the TTS.

\paragraph{Retraction rules}
The first thing we want to allow, is rewriting a term of type |A| to a term of type |R| and vise 
versa. This is done by two functions, |rep :: A -> R| and |abs :: R -> A|, which the user has to 
provide. These functions should have the property that |abs `comp` rep = id| and thus enable the 
transform system to change any type |A| into an |R| and back, while maintaining the same semantics. 

Two types |A| and |R| for which we can define the two functions |abs| and |rep| are called a retraction. More
about the theory behind retractions can be found in\cite{meyer}.

\paragraph{Rewriting rules}
We also want to allow the rewriting of already present terms. These rewrite rules can be put in the
environment |G|. This allows the user to specify the rewriting of variable |x| into |x'|. 
However, not all rewrites are allowed here. A rewrite rule should satisfy the following properties:

> typeOf(x) = <<F>>A
> typeOf(x') = <<F>>R
> dimap_F rep abs x' = x

These rules will ensure that in the end the transformation will be semantics preserving. The typing properties
can easily be checked by the TTS system itself, the term equivalence will have to be assured by the user of
the system. Why these properties are important will become more clear when we proof the system correct. The
environment |G| can also be used to define ordinary external variables by supplying an identity transformation
for such as variable (|x `rw` x : ty|).


\subsection{Typing system}
We now have the basic ingredients to define our TTS. The system is defined in Figure~\ref{fig:stlcrules}. 
The |Var|, |Abs| and |App| rule are very similar to the rules in STLC, except with
an extra term and the functor instead of a type. These rules form the identity rules. If no rewrite would be applied
these rules yield the identity transformation.

Shadowing on the rewrite environment |G| removes the rewrite rules which have a matching source and/or target term. This
makes sure we do not apply rewrite rules to newly introduced variables, only to global definitions.

The |RWVar| rule rewrites a variable using a user-specified rule. The |Rep| and |Abs| rules can rewrite any term
which is of the correct type. The |Final| rule in Figure~\ref{fig:stlcfinal} finalizes a transformation and concludes
that both terms are semantically equal. This is only the case when there are no free variables and the type of the source
and target terms are equal.

\begin{figure}[t]
\begin{align*}
&|Var|
&\quad
&\inferrule{|x `rw` x' : F `elem` G|}
           {|G +- x `rw` x' : F|}
\\
&|Lambda|
&\quad
&\inferrule{|Gx, x `rw` x : F_a +- e `rw` e' : F_r|}
           {|G +- \x. e `rw` \x. e' : F_a -> F_r|}
\\
&|App|
&\quad
&\inferrule{|G +- f `rw` f' : F_a -> F_r| \\\\
            |G +- e `rw` e' : F_a|}
           {|G +- f e `rw` f' e' : F_r|}
\\
&|Rep|
&\quad
&\inferrule{|G +- e `rw` e' : A|}
           {|G +- e `rw` rep e' : Id|}
\\
&|Abs|
&\quad
&\inferrule{|G +- e `rw` e' : Id|}
           {|G +- e `rw` abs e' : A|}
\\
&|Judgement|
&\quad
&\boxed{|G +- e `rw` e' : F|}
\end{align*}
\caption{Type checking rules for the propagation relation}
\label{fig:stlcrules}
\end{figure}

\begin{figure}[t]
\begin{align*}
&|Final|
&\quad
&\inferrule{|G +- e `rw` e' : F| \\\\ 
            |forall x `rw` x' : F_2 `elem` G, dimap_F2 rep abs x' == x| \\\\
            |<<F>>A = <<F>>R|}
           {|e == e'|}
\end{align*}
\caption{Final rule to establish the equality between terms}
\label{fig:stlcfinal}
\end{figure}

The next step is to turn these typing rules into an algorithm which will actually do a
transformation. This will be done in the next section. We would also like to see proof 
that these rules only allow semantics preserving transformations. The proof of this can be found in appendix A.

\section{Implementation}
Although the rules in Figure~\ref{fig:stlcrules} are based on STLC, the rules are not syntax
directed any more, because we have added extra rules to allow for transformations. Thus implementing
an algorithm which performs a transformation using these rules becomes a form of proof search. We have to
create an algorithm which, when provided with user-defined transformations and an input program, will
search through all valid derivations and return the `best` result, for some definition of best.

\subsection{Bottom-up typing}
Our algorithm works by producing all transformations in a bottom-up fashion. Normal type inference, however,
does not work in a bottom up way. We need a different procedure to infer the types of terms if we want 
bottom-up transformation to work.

We use a bottom-up typing algorithm based on the work by Heeren et al\cite{heeren}. In this approach the
typing system collects type constraints, and tries to solve these constraints. If the
constraints are unsolvable, we have an ill-typed program. We use a somewhat simpler version here because
we do not yet include let-polymorphism, but the ideas are the same. What we get is a bottom-up monomorphic
functor inference algorithm. To do inference, we need to add functor variables to the functor definition:

> F ::= Id | T | beta | F -> F

We replace the typing environment |G| with an constant environment |G|, an assumption environment |A| and 
constraint environment |C|. The constant environment contains external definitions. The assumption environment 
contains the functor variables we have assumed for all unbound variables, the constraint
environment collects constraints on the functor variables. They are both sets of the following form:

> AS := empty | AS, x : a
> C := empty | C, F_1 == F_2

The constraint set can be partly solved to obtain a functor substitution which satisfies the used
constraints. This is expressed by the |solve| function. |solve| needs a unification procedure
(|mgu|) for functors. Unification on functors is the same as for normal types. The extra |Id| functor 
is treated like a base type.

> solve :: C -> (sub, C)
> solve(empty)             =  (id, empty)
> solve(C_1, F_1 == F_2)   =  let   sub_1 = mgu F_1 F_2
>                                   (sub_2, C_2) = solve sub_1(C_1)
>                             in    (sub_2 `comp` sub_1, C_2)

If |mgu| fails, |solve| fails and we have an ill-typed transformation. We also add
a solver rule, which uses |solve| to solve the constraints as far as possible and updates
the inferred functor and assumptions environment:

\begin{center}
  \inferrule{|(sub, C_2) = solve C_1|}
            {|`sol` (AS, C_1, F) `solve` (sub AS, C_2, sub F)|}
\end{center}

\subsection{Propagation and transformation}
Next to adding bottom up typing, we also make a subdivision of the type inference rules into two 
categories: the propagation relation and the transformation relation.

The propagation relation consists of the syntax-directed rules of the transformation system and will
be used in the algorithm to guide the transformation process. They can be found in Figure~\ref{fig:stlcprop}.
We now have two |Var| rules instead of one. The normal |Var| rule does inference of locally bound variables,
while the |RWVar| rule applies external transformations and constants. Except for the |RWVar| rule these rules 
do not actually do any transformation. If the environment |G| is empty, these rules are the identity transformation. 

\begin{figure}[t]
\begin{align*}
&|Var|
&\quad
&\inferrule{ }
           {|G; {x : beta}; empty `pro` x `rw` x : beta|}
\\
&|Lambda|
&\quad
&\inferrule{|Gx; AS; C `tr` e `rw` e' : F_r| \\\\
            |C_1 = C `union` {beta' == beta || x : beta' `elem` AS}| \\\\
            |`sol` (ASx, C_1, beta -> F_r) `solve` (AS', C_2, F)|}
           {|G; AS'; C_2 `pro` \x. e `rw` \x. e' : F|}
\\
&|App|
&\quad
&\inferrule{|G; AS_1; C_1 `tr` f `rw` f' : F_1| \\\\
            |G; AS_2; C_2 `tr` e `rw` e' : F_2| \\\\
            |C' = C_1 `union` C_2 `union` {F_1 == F_2 -> beta}| \\\\
            |`sol` (AS_1 `union` AS_2, C', beta) `solve` (AS, C, F)|}
           {|G; AS; C `pro` f e `rw` f' e' : F|}
\\
&|RWVar|
&\quad
&\inferrule{|x `rw` x' : F `elem` G|}
           {|G; empty; empty `pro` x `rw` x' : F|}
\\
&|Judgement|
&\quad
&\boxed{|G; AS; C +- e `rw` e' : F|}
\end{align*}
\caption{Type inference rules for the propagation relation}
\label{fig:stlcprop}
\end{figure}

The rules in the transformation relation can be found in Figure~\ref{fig:stlctrans}. These rules are not directed 
by syntax and could potentially be applied infinitely many times. The reason we make a distinction between these 
two categories is to avoid this infinite application of rewrite rules, as such:

> e `rw` rep (abs (rep (abs e)))

This is a correct transformation according to the typing rules, but unwanted in practice. Thus we force that after
each transformation rule, a propagation rule is applied to move the transformation forward. We add the |Id| rule
to the transformation relation to allow for identity transformations.

\begin{figure}[t]
\begin{align*}
&|Rep|
&\quad
&\inferrule{|G; AS; C `pro` e `rw` e' : F| \\\\
            |`sol` (AS, C `union` {F == A}, F) `solve` (AS', C', _)|}
           {|G; AS'; C' `tr` e `rw` rep e' : Id|}
\\
&|Abs|
&\quad
&\inferrule{|G; AS; C `pro` e `rw` e' : F| \\\\
            |`sol` (AS, C `union` {F == Id}, F) `solve` (AS', C', _)|}
           {|G; AS'; C' `tr` e `rw` abs e' : A|}
\\
&|Id|
&\quad
&\inferrule{|G; AS; C `pro` e `rw` e' : F|}
           {|G; AS; C `tr` e `rw` e' : F|}
\end{align*}
\caption{Rewrite derivations in the transformation relation}
\label{fig:stlctrans}
\end{figure}

The final rule is adapted to work with the new type system, as can be seen in 
Figure~\ref{fig:stlcinferencefinal}
\begin{figure}[t]
\begin{align*}
&|Final|
&\quad
&\inferrule{|G; AS; C `tr` e `rw` e' : F| \\\\
            |`sol` (AS, C, F) `solve` (empty, empty, F')| \\\\ 
            |<<F'>>A = <<F'>> R|}
           {|e = e'|}
\end{align*}
\caption{Final rule to establish the equality between terms}
\label{fig:stlcinferencefinal}
\end{figure}

\subsection{String continuation transformation}
With this simple transformation system in place, we can define our first transformation. As an example we 
will describe a transformation system for Hughes' string continuation transformation\cite{hughes}. This is a transformation
which optimizes string concatenation by treating Strings as String continuations of the form |String -> String|.

We first have do define the type |A| and |R|, the types the system will transform.

> A = String
> R = String -> String

Now we need the conversion functions |rep| and |abs|, to convert between the types. 

> rep = (++)
> abs = \k -> k ""

We also need to make sure that these functions adhere to the retraction law |forall x. abs (rep x) == x|.

>  abs (rep x)
>= { Def rep }
>  abs ((++) x)
>= { Def abs }
>  (\k -> k "") ((++) x)
>= { Evaluation }
>  x ++ ""
>= { Definition (++) }
>  x

Finally, we can define the transformations we want to perform in the environment |G|. The string continuation
transformation works by replacing |++| by |`comp`|. We can easily express this:

> F = Id -> Id -> Id
> G = { (++) `rw` (`comp`) : F }

Now we only have to show the required law on transformations: |dimap_F rep abs (`comp`) == (++)|. The
functor definition for |dimap_F| is as follows:

> dimap_F :: (a -> b) -> (b -> a) -> F b -> F a
> dimap_F rep abs f = \x y -> abs $ f (rep x) (rep y)

>  dimap_F rep abs (`comp`)
>= { definition dimap_F }
>  \x y -> abs $ (`comp`) (rep x) (rep y)
>= { definition rep, evaluation }
>  \x y -> abs $ (`comp`) (x ++ ) (y ++)
>= { definition abs, evaluation }
>  \x y -> ((`comp`) (x ++ ) (y ++)) ""
>= { definition (`comp`) }
>  \x y -> x ++ (y ++ "")
>= { definition ++ }
>  \x y -> x ++ y
>= { Eta reduction }
>  (++)

>  \x y -> (`comp`) (rep x) (rep y)
>== { Def rep } 
>  \x y -> (`comp`) (x ++) (y ++)
>== { Def comp }
>  \x y -> x ++ y ++
>== { Def rep }
>  \x y -> rep (x ++ y)

\section{Transforming compound expressions}
The transformation rules in the basic STLC TTS are already powerful, but still rather limited. The
biggest shortcoming is that they only allow for rewriting single variables, not compound terms. In this
section we will introduce an extension to the basic STLC TTS to allow for such transformations.

Compound rewrites are pattern-based. The user can define patterns to match and how these patterns
should be rewritten. We define patterns as follows, where |m| represents metavariables:

> p := p p | x | m

We do not allow lambda abstractions, this would allow the user to rename or change bindings, something which
is currently not supported by the TTS. We use these patterns to rewrite one into another,
as defined in the following environment.

> env := empty | env, p1 `rw` p2

Rewriting is done by pattern matching on the first term, and if successful, filling in the bound meta variables
into the second term. Pattern matching and application are defined in Figure~\ref{fig:patternmatching} and
~\ref{fig:patternapplication}. 

\Bram{TODO: Work this out more}
\begin{figure}[t]
\begin{align*}
\inferrule{|forall S, D, G|\\\\
           |P = mkSub(D)| \\\\
           |G; D `app` S @ p1 => e1 : F_1 R| \\\\
           |G; D `app` S @ p2 => e2 : F_2 R| \\\\
           |F_1 A == F_2 A| \\\\
           |->| \\\\
           |dimap_F1 rep abs sub_P(e1) = dimap_F2 rep abs sub_P(e2)|}
          {|p1 `rw` p2|}
\end{align*}
\caption{Admissibility of a pattern rewrite rule}
\label{fig:patternrewrite}
\end{figure}

\begin{figure}[t]
\begin{align*}
&|Transform|
&\quad
&\inferrule{|p1 `rw` p2 `elem` env|\\\\ 
            |G; D `pro` e `rwe` e' : F_1| \\\\
            |G; D `rwr` p1 `rw` p2 => e' : ty `rw` e'' : ty'|}
           {|G; D `tr` e `rwe` e'' : F_2|}
\end{align*}
\caption{Apply a rewrite rule to the transformation}
\label{fig:transform}
\end{figure}

\begin{figure}[t]
\begin{align*}
\\
&|MVar|
&\quad
&\inferrule{|_ `rw` x : F `elem` G|}
           {|G `mat` x @ x : F => id|}
\\
&|MMVar|
&\quad
&\inferrule{|G; R `union` D R `ty` e : F R|}
           {|G; D `mat` m @ e : F R => {m +-> (e, F R)}|}
\\
&|MApp|
&\quad
&\inferrule{|G; D `mat` p1 @ e1 : F_a R -> F_r R => S1| \\\\
            |G; D `mat` p2 @ e2 : F_a R => S2|}
           {|G; D `mat` p1 p2 @ e1 e2 : F_r R => S1 `comp` S2|}
\\
&|Judgement|
&\quad
&\boxed{|G; D `mat` p @ e : F R => sub|}
\end{align*}
\caption{Typed pattern matching}
\label{fig:patternmatching}
\end{figure}

\begin{figure}[t]
\begin{align*}
\\
&|AVar|
&\quad
&\inferrule{|_ `rw` x : F R `elem` G|}
           {|G; D `app` S @ x => x : F R|}
\\
&|AMVar|
&\quad
&\inferrule{|S m = (e, F R)|}
           {|G; D `app` S @ m => e : F R|}
\\
&|AApp|
&\quad
&\inferrule{|G; D `app` S @ p1 => e1 : F_a R -> F_r R| \\\\
            |G; D `app` S @ p2 => e2 : F_a R|}
           {|G; D `app` S @ p1 p2 => e1 e2 : F_r R|}
\\
&|Judgement|
&\quad
&\boxed{|G; D `mat` p @ S => e : F R|}
\\
\end{align*}
\caption{Typed pattern application}
\label{fig:patternapplication}
\end{figure}

\begin{figure}[t]
\begin{align*}
&|Rewrite|
&\quad
&\inferrule{|G; D `mat` p1 @ e1 : F_1 R => S| \\\\
            |G; D `app` S @ p2 => e2 : F_2 R| \\\\
            |F_1 A = F_2 A|
           }
           {|G; D `rwr` p1 `rw` p2 @ e1 : F_1 R => e2 : F_2 R|}
\\
&|Judgement|
&\quad
&\boxed{|G; D `rwr` p1 `rw` p2 @ e1 : F_1 R => e2 : F_2 R|}
\\
\end{align*}
\caption{Typed rewriting}
\label{fig:typedrewriting}
\end{figure}

\section{Generalizing to let-polymorphism with simple datatypes}
In this chapter we will create the TTS for a more powerful language: The let-polymorphic
lambda calculus with datatypes. This system has some substantial extensions with respect to the STLC
version, but the core ideas remain the same. First we define our object language:

> e    ::= x | c | e e | \x. e | fix e | let x = e in e
> ty   ::= al | ty -> ty | ty | ty ty
> sch  ::= forall all. ty

We limit the types |T| to be exponential types with existentials, so no GADTs. We do not not specify the way
in which data types and defined and eliminated, this is independent of the system.

\subsection{The let-poly TTS}
Just as with the STLC version, we create a functor type with |Id| representing a hole. We want to allow the
transformation of parametrized types, so we allow for type application.

> F    ::= Id | T | al | F -> F | F F
> sch  ::= forall all. F

We also define the interpretation function for this extended functor.

> <<Id>>ty               = ty
> <<T>>ty                = T
> <<al>>ty               = al
> <<F_1 -> F_2>>ty       = <<F_1>>ty -> <<F_2>>ty
> <<F_1 F_2>>ty          = <<F_1>>ty <<F_2>>ty
> <<forall all. sch>>ty  = forall al. <<sch>>ty

The environment |G| now binds schemas instead of types, the rest remains the same:

> G  ::= empty | G, x `rw` x' : sch

The definition of |dimap| is complicated by the fact that we are now allowing type application. For
this we need to be able to use a |dimap| over normal datatypes. This is why we restricted the data types
of our object language to exponential types. Thus we can be sure that a |dimap| exists for those types.

> dimap_F :: (T_a -> T_b) -> (T_b -> T_a) -> <<F>>Tb -> <<F>>Ta
> (dimap(Id))             rep abs x = abs x
> (dimap(T))              rep abs x = x
> (dimap(al))             rep abs x = x
> (dimap(F_1 -> F_2))     rep abs f = dimap_F2 rep abs `comp` f `comp` dimap_F1 abs rep
> (dimap(F_1 F_2))        rep abs x = (dimap(<<F_1 F_2>>Ta)) (dimap_F2 rep abs) (dimap_F2 abs rep) `comp` dimap_F1 rep abs x
> (dimap(forall all. F))  rep abs x = dimap_F rep abs x

\subsection{Dealing with polymorphism}
The let-polymorphic lambda calculus defines functions on the types to deal with
quantification, |ftv :: ty -> all|, |gen :: ty -> sch| and |inst :: sch -> ty|. The functor version of 
these functions is essentially the same, |Id| is treated as a normal type constructor.

\subsection{Rewrite rules}
The setup of the user-supplied rewriting rules is essentially the same for let-poly as for STLC,
there is just a more complicated underlying language. We do rewriting from a term of type |A all| to a term of type |R all| 
using the functions |rep :: A all -> R all| and |abs :: R all -> A all|, which the user has to 
provide.  We also construct the same rewriting environment |G| which has to uphold the same laws.
With for all |x `rw` x' `elem` G|:
 
> typeOf(x) = <<F>>Ta
> typeOf(x') = <<F>>Tr
> dimap_F rep abs x' = x

\subsection{Typing system}
With all this groundwork laid out, we can now define the actual typing system for the let-polymorphic TTS. The rules
can be found in Figure~\ref{fig:letpolyrules}. The |Var| does instantiation of schemas, the let rule does the generalization.

The extended type language does not show up here, because this is hidden by the functor and the functions on functors.

\begin{figure}[t]
\begin{align*}
&|Var|
&\quad
&\inferrule{|x `rw` x' : sch `elem` G|}
           {|G +- x `rw` x' : inst(sch)|}
\\
&|Lambda|
&\quad
&\inferrule{|Gx, x `rw` x : F_a +- e `rw` e' : F_r|}
           {|G +- \x. e `rw` \x. e' : F_a -> F_r|}
\\
&|App|
&\quad
&\inferrule{|G +- f `rw` f' : F_a -> F_r| \\\\
            |G +- e `rw` e' : F_a|}
           {|G +- f e `rw` f' e' : F_r|}
\\
&|Let|
&\quad
&\inferrule{|G +- e1 `rw` e1' : F_1| \\\\
            |Gx, x `rw` x : gen(F_1) +- e2 `rw` e2' : F_2| }
           {|G +- let x = e1 in e2 `rw` let x = e1' in e2' : F_2|} 
\\
&|Fix|
&\quad
&\inferrule{|G +- e `rw` e' : F -> F|}
           {|G +- fix e `rw` fix e' : F|}
\\
&|Rep|
&\quad
&\inferrule{|G +- e `rw` e' : A (vec (F))|}
           {|G +- e `rw` rep e' : Id (vec (F))|}
\\
&|Abs|
&\quad
&\inferrule{|G +- e `rw` e' : Id (vec (F))|}
           {|G +- e `rw` abs e' : A (vec (F))|}
\\
&|Judgement|
&\quad
&\boxed{|G +- e `rw` e' : F|}
\end{align*}
\caption{Type checking rules for the propagation relation}
\label{fig:letpolyules}
\end{figure}

\section{Implementation of let-poly}

\section{List fusion transformation}
The let-polymorphic version of the TTS system is powerful enough to enable us to express the
transformations underlying list-fusion. List-fusion is an optimization which views lists as streams
of data and avoids expensive intermediate lists that may be constructed between functions.



> -- Normal lists
> data [a] = [] | a : [a]
> 
> -- Streams
> data Step s a =
>    Done
>  | Yield a s
>  | Skip s
> 
> data Stream a = some s. Stream (s -> Step s a) s
>
> toStream :: [a] -> Stream a
> toStream l = Stream next l
>   where
>     next []     = Done
>     next (x:xs) = Yield x xs
>
> fromStream :: Stream a -> [a]
> fromStream (Stream next seed) = extract seed
>   where
>     extract s = case next s of
>       Done       -> []
>       Skip    s' -> extract s'
>       Yield x s' -> x : extract s'

We first have to show that |toStream| and |fromStream| form a retraction pair. We show
this by induction on the list argument.

Empty list:

> fromStream (toStream [])
>== { Definition toStream }
> fromStream (Stream next [])
>== { Definition fromStream }
> extract []
>== { Definition extract and next }
> []

Cons case:

> fromStream (toStream (x : xs))
>== { Definition toStream }
> fromStream (Stream next (x : xs))
>== { Definition fromStream }
> extract (x : xs)
>== { Definition extract and next }
> x : extract xs
>== { Defintition fromStream }
> x : fromStream (Stream next xs)
>== { Defintion toStream }
> x : fromStrean (toStream xs)
>== { Induction hypothesis }
> x : xs

We can now define the retraction for the transformation system:

> A a = [a]
> R a = Stream a
> rep = toStream
> abs = fromStream

We need both the polymorphism and the parametrized types to make this example work. Not that this
system also support nested application of transformation, so a term of type |[[Int]]| could be
transformed to the type |Stream (Stream Int)|.

The actual optimization in this transformation comes from the rewriting of functions which make
use of the optimized stream structure. We give an example of map here with the proof:

> map :: (a -> b) -> [a] -> [b]
> map f [] = []
> map f (x : xs) = f x : map f xs
>
> mapS :: (a -> b) -> Stream a -> Stream b
> mapS f (Stream next seed) = Stream next' seed
>     next' s =
>       case next s of
>           Done       -> Done
>           Skip s'    -> Skip s'
>           Yield a s' -> Yield (f a) s'

From this we can make the following transformation rule:

> F = (a -> b) -> Id a -> Id b
> map `rw` mapS : F

However, we first have to show that |mapS| is a proper implementation for |map|, by showing:

> dimap_F rep abs mapS f x == map f x

> dimap_F toStream fromStream mapS f x
>== { Definition dimap_F }
> ((dimap(Id a -> Id b)) rep abs `comp` mapS `comp` (dimap(a -> b)) abs rep) f x
>== { Evaluation }
> ((dimap(Id a -> Id b)) rep abs $ mapS $ (dimap(a -> b)) abs rep f) x
>== { Definition (dimap(Id a -> Id b)) }
> ((dimap(Id b)) rep abs `comp` (mapS $ (dimap(a -> b)) abs rep f) `comp` (dimap(Id a)) abs rep) x
>== { Evaluation }
> (dimap(Id b)) rep abs $ (mapS $ (dimap(a -> b)) abs rep f) $ (dimap(Id a)) abs rep x
>== { Defintition dimap }
> (dimap([b])) rep abs $ abs $ (mapS $ (dimap(a -> b)) abs rep f) $ (dimap(Stream a)) abs rep $ rep x

We now proof by induction on x


\appendix
\section{Correctness of STLC}
In this section we will show that a transformation using the STLC TTS results in a program semantically
equal to the source program. To show this, we first show an important property which holds for TTS
transformations, we then use this property to actually proof the semantic equivalence.

\subsection{Identity theorem}
From the retraction law we know that |abs `comp` rep == id|. In general, the opposite |rep `comp` abs == id| is
not the case. In this section we will show that for all terms within our transform system, this actually is the case.
For all derivation of the form:

> G +- e `rw` e' : Id

We will proof that.

> rep (abs e') == e'

We will proof this by first proving another lemma, concerning the possible evaluation results
of |e'|:

> </e'/> == rep t

Where |</e'/>| means full normalization of the term |e'|. In other words, we will show that after
normalization, |e'| is semantically equivalent to |rep t| for some |t|. Knowing this, we
can derive the property as follows:

> rep (abs e')
>== { Evaluation }
> rep (abs </e'/>)
>== { Lemma }
> rep (abs (rep t))
>== { Retraction }
> rep t
>== { Lemma }
> </e'/>
>== { Evaluation }
> e'

\paragraph{Lemma}
For proving |</e'/> == rep t| we will look at the possible terms which can introduce a term
of type |Id|. By the definition of the TTS system, |Id| can only be introduced by rep |rep :: A -> Id|
or any of the user supplied transformation rules which are of the form |e `rw` e' : F|. Because we 
look at |e'| after normalization, we do not have to consider variables, abstractions of applications.

The rep case follows easily:
> </rep e/> = rep e

For rewrites of the form |e `rw` e' : F| we know that |dimap_F id rep e == dimap_F rep id e'| from the
premises. We only look at rewrites for which |e' (vec(v)) :: Id|.
> </e' (vec(v))/> = rep x


> e' (vec(v))
>== { Induction hypothesis, all arguments of type Id are built with rep }
> dimap_F rep id e' $ (vec(v'))
>== { Premise }
> dimap_F id rep e $ (vec(v'))
>== { Result type is Id, so rep is applied }
> rep x

\subsection{Equality property}
We will show that for any derivation of the form:

> G +- e `rw` e' : F

The following property holds:

> dimap_F G rep abs e' = e

Here |dimap_F G| is the term-level functor for |F| under some environment |G|. We have to incorporate
the environment into the equation here, because |e| and |e'| can contain free variables and they
behave differently in different environments. |dimap_F G| is defined as follows:

> dimap_F :: G -> (a -> b) -> (b -> a) -> <<F>>b -> <<F>>a
> dimap_F G rep abs v = dimap_F rep abs v @ mkSub G

Here |@| means simultaneous substitution. The substitution is what allows us to reason about free variables. |mkSub|
is defined in the following way:

> mkSub :: G -> sub
> mkSub (G, x `rw` x' : F)  = [x'/dimap_F abs rep x] `comp` mkSub G
> mkSub empty             = id


\subsection{Proof of equality}
The |Final| rule constructs the actual proof that |e| and |e'| are equal, provided we can prove the
previous property.

\begin{center}
\inferrule{|G; empty +- e `rw` e' : F| \and |<<F>>A == <<F>>R|}
          {|e = e'|}
\end{center}
From the premises we get the following property:

> dimap_F rep abs (sub_P(e')) = e

|D| is empty, so this is equal to:

> dimap_F rep abs e' = e

Because |<<F>>A == <<F>>R|, |F| does not contain any holes, so |F| is a base-type |ty|. From the definition of 
|dimap_F| we can see that a functor on base types yields the identity function on the term level, as such:

> dimap_ty :: (a -> b) -> (b -> a) -> <<F_ty>>b -> <<F_ty>>a
> dimap_ty _ _ = id

This enables us to prove the equality |e == e'|

> dimap_F rep abs e' = e
>=> { dimap_F == dimap_ty }
> dimap_ty rep abs e' = e
>=> { Definition dimap_ty }
> id e' = e
>=> { Def id }
> e' = e

This proofs, that if a transformation result is a closed term and the source and result types are equal, the semantics of
the source and the result term are equal.

\subsection{Inference rule properties}
What is left is to proof that the property is preserved by all derivation rules. Of course, this assumes that
the user has supplied a transformation which adheres to the required properties.

\subsubsection{Var rule}

\begin{center}
\inferrule{|x `rw` x' : F `elem` G|}
          {|G +- x `rwe` x' : F|}
\end{center}

We have to proof |dimap_F G rep abs x' == x|

>  dimap_F G rep abs x'
>== {|x `rw` x' : F `elem` G|}
>  dimap_F (Gx, x `rw` x' : F_a) rep abs x'
>== { Definition dimap_F G }
>  dimap_F rep abs x' @ mkSub (Gx, x `rw` x' : F_a)
>== { Definition mkSub }
>  dimap_F rep abs x' @ [x'/dimap_F abs rep x] `comp` mkSub Gx
>== { Apply substitution }
>  dimap_F rep abs x' @ [x'/dimap_F abs rep x] `comp` mkSub Gx
>== { Definition mkSub }
>  dimap_F rep abs (dimap_F abs rep x) @ mkSub Gx
>== { No eligible substitution in Gx }
>  dimap_F rep abs (dimap_F abs rep x)
>== { Functor composition }
>  dimap_F (abs `comp` rep) (abs `comp` rep) x
>== { Retraction identity }
>  dimap_F id id x
>== { Functor identity }
>  x

\subsubsection{Abstraction rule}

\begin{center}
\inferrule{|Gx; x `rw` x : F_a +- e `rwe` e' : F_r|}
          {|G +- \x. e `rwe` \x. e' : F_a -> F_r|}
\end{center}

We have to proof the following equivalence:

> (dimap(F_a -> F_r)) G rep abs (\x. e') == \x. e

From the premises we know that:

> dimap_Fr (Gx, x `rw` x : F_a) rep abs e' == e

Proof:

>  (dimap(F_a -> F_r)) G rep abs (\x. e')
>== { Definition (dimap(F_a -> F_r)) G }
>  (dimap(F_a -> F_r)) rep abs (\x. e') @ mkSub G
>== { Commute substitution over lambda }
>  (dimap(F_a -> F_r)) rep abs (\x. e' @ mkSub Gx)
>== { Definition dimap }
>  dimap_Fr G rep abs `comp` (\x. e' @ mkSub Gx) `comp` dimap_Fa G abs rep
>== { Eta expansion }
>  (\x. dimap_Fr G rep abs `comp` (\x. e' @ mkSub Gx) `comp` dimap_Fa G abs rep $ x)
>== { Evaluation }
>  (\x. dimap_Fr rep abs (e' @ [x/dimap_Fa abs rep x] `comp` mkSub Gx)
>== { Definition mkSub }
>  (\x. dimap_Fr rep abs e' @ mkSub (Gx, x `rw` x : F_a))
>== { Definition dimap }
>  (\x. dimap_Fr (Gx, x `rw` x : F_a) rep abs e')
>== { Premisse }
>  (\x. e)

\subsubsection{Application rule}
\begin{center}
\inferrule{|G +- f `rwe` f' : F_a -> F_r | \\\\
           |G +- e `rwe` e' : F_a |}
          {|G +- f e `rwe` f' e' : F_r|}
\end{center}

We have to proof the following equality:

> dimap_Fr G rep abs (f' e') == f e

From the premises we know that:

> dimap_F G rep abs f'  == f
> dimap_Fa G rep abs e' == e

Proof:

>  dimap_Fr G rep abs (f' e')
>== { Definition dimap_Fr G }
>  dimap_Fr rep abs (f' e') @ mkSub G
>== { Property below }
>  dimap_F rep abs f' (dimap_FA rep abs e') @ mkSub G
>== { Distribute substitution }
>  dimap_F rep abs f' @ mkSub G (dimap_FA rep abs e' @ mkSub G)
>== { Definition dimap }
>  dimap_F G rep abs f' (dimap_FA G rep abs e')
>== { Induction hypotheses }
>  f e

Extra property |dimap_Fr rep abs (f' e') == (dimap(F_a -> F_r)) rep abs f' (dimap_Fa rep abs e')|

>  (dimap(F_a -> F_r)) rep abs f' (dimap_Fa rep abs e')
>== { Definition of dimap }
>  dimap_Fr rep abs $ f' $ dimap_Fa abs rep $ dimap_FA rep abs e'
>== { Functor composition }
>  dimap_FR rep abs $ f' $ dimap_Fa (rep `comp` abs) (rep `comp` abs) e'
>== { rep . abs :: i == id }
>  dimap_Fr rep abs $ f' $ dimap_Fa id id e'
>== { Functor identity }
>  dimap_Fr rep abs (f' e')

\subsubsection{Rep rule}
Applying rep to some source term results in a term which can be made equal to the source term
by applying abs to it. This is reflected in the reasoning below.

\begin{center}
\inferrule{|G +- e `rwe` e' : A|}
          {|G +- e `rwe` rep e' : Id|}
\end{center}

We need to proof that |dimap_Id G rep abs (rep e') == e|. From the premises we know
that |dimap_A G rep abs e' == e|.

>  dimap_Id G rep abs (rep e')
>== { Definition dimap_Id G }
>  dimap_Id rep abs (rep e') @ mkSub G
>== { Definition dimap_Id }
>  abs (rep e') @ mkSub G
>== { Retraction }
>  e' @ mkSub G
>== { Identity function }
>  id e' @ mkSub G
>== { Definition dimap_A  }
>  dimap_A rep abs e' @ mkSub G
>== { Definition dimap_A G }
>  dimap_A G rep abs e'
>== { Premisse }
>  e
 
\subsubsection{Abs rule}
Applying abs to a suitable term equalizes the result and source term.
          
\begin{center}
\inferrule{|G +- e `rwe` e' : Id|}
          {|G +- e `rwe` abs e' : A|}
\end{center}

We have to proof |dimap_A G rep abs (abs e') == e|. From the premises we know
that |dimap_Id G rep abs e' == e|.

>  dimap_A G rep abs (abs e')
>== { Definition dimap_A G }
>  dimap_A rep abs (abs e') @ mkSub G
>== { Definition dimap_A }
>  abs e' @ mkSub G
>== { Definition dimap_Id }
>  dimap_Id rep abs e' @ mkSub G
>== { Defintion dimap_Id G }
>  dimap_Id G rep abs e'
>== { Premise }
>  e

\subsubsection{Transform rule}

\begin{center}
\inferrule{|p1 `rw` p2 `elem` env|\\\\ 
           |G; D +- e `rwe` e' : F_1| \\\\
           |G; D `rwr` p1 `rw` p2 => e' : F_1 R `rw` e'' : F_2 R|
          }
          {|G; D `tr` e `rwe` e'' : F_2|}
\end{center}

From the |Rewrite| premise we get the assertions that

> F_1 A = F_2 A
> dimap_F1 rep abs sub_P(e) = dimap_F2 rep abs sub_P(e')

From this we can see that the type of e is still valid after transformation (|F_1 A == F_2 A|).
For the terms the proof also follows easily.

>  dimap_F2 rep abs sub_G(e'')
>= { Premisse `rwr` }
>  dimap_F1 rep abs sub_G(e')
>= { Premisse `tr` }
>  e

\subsubsection{Rewrite rule}

\begin{center}
\inferrule{|G; D `mat` p1 @ e1 : F_1 R => S| \\\\
           |G; D `app` S @ p2 => e2 : F_2 R| \\\\
           |F_1 A = F_2 A|
           }
           {|G; D `rwr` p1 `rw` p2 @ e1 : F_1 R => e2 : F_2 R|}
\end{center}

First We have to proof that |F_1 A = F_2 A|, this follows easily from the premises.

The second thing we have to show is that:

> dimap_F1 rep abs sub_P(e) = dimap_F2 rep abs sub_P(e')

We have restricted the user to only allow rewrite rules which abide the following law:

\begin{center}
\inferrule{|forall S, D, G| \and |P = mkSub(D)| \\\\
           |G; D `app` S @ p1 => e1 : F_1 R| \\\\
           |G; D `app` S @ p2 => e2 : F_2 R| \\\\
           |F_1 A == F_2 A| \\\\
           |->| \\\\
           |dimap_F1 rep abs sub_P(e1) = dimap_F2 rep abs sub_P(e2)|}
          {|p1 `rw` p2|}
\end{center}           

Thus is we can proof the entire top side of the implication, we know that the desired law holds. |F_1 A == F_2 A|
follows from the premises. |G; D `app` S @ p2 => e2 : F_2 R| also follows directly. 

To proof |G; D `app` S @ p1 => e1 : F_1 R|, we need the following lemma:

> G; D `mat` p1 @ e1 : F_1 R => S 
>    -> 
> G; D `app` S @ p1 => e1 : F_1 R

Eg. Mathing and then applying yields the same term. This is easy to see from the symmetric
nature of matching and applying of patterns.

We can proof the left side of this implication, so we have our proof for |G; D `app` S @ p1 => e1 : F_1 R|


\appendix
\section{Functors for existentials}

%-------------------------------------------------------------------------------
\bibliographystyle{abbrvnat}
\bibliography{thesis}

\end{document}

