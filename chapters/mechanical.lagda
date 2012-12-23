%include ../formatting/agda.fmt

\section{STLC object language}

Fundamental to a mechanical formalization of the TTS system is the representation of the object language, STLC. STLC can be represented in multiple ways, as described in~\cite{keuchel11}. The essential choice is between a Higher Order Abstract Syntax and a de Bruijn representation. Although HOAS terms can be constructed in Agda, Agda is not strong enough to reason about semantic equivalence of HOAS terms, unlike other languages such as Twelf~\cite{schurmann08}. The representation chosen here is a first-order representation using well-typed de Bruijn indices as found in Keller and Altenkirch~\cite{keller10}. A first-order formulation is mandatory because it allows full inductive reasoning over terms and types in the object language and thus reasoning about the semantics. Formulating using well-typed de Bruijn indices is useful because it asserts important properties about the terms by construction.

\paragraph{De Bruijn indices} is a way to represent variables in languages based on the lambda calculus. Instead of naming a variable, a variable is given an index which denotes at which lambda the variable is bound. More precisely, the index denotes the number of lambdas that occur between the variable and its binding site. \emph{Well-typed} de Bruijn indices are an extension of this idea: each variable now has a type associated with its binding site. When a term contains free variables, a context is used to assign each free variable a type and a binding place. Types and contexts are defined in the following way:

%include ../proof/STLC/Context/Base.lagda
%include ../proof/STLC/Types/Base.lagda

Because variables are nameless in the de Bruijn representation, each item in the type context |Con| represents a consecutive binding site for free variables and the type that is associated with it. Variable indices are defined as indices into this surrounding context.

%include ../proof/STLC/Variable/Base.lagda

Using these constructions we can construct a representation for the simply typed lambda calculus.

%include ../proof/STLC/Term/Base.lagda

Terms are indexed by a context representing the free variables it may contain, along with the resulting type of the term itself. A variable is represented by an index into the context and produces a term with the type of that variable. A lambda binding binds a free variable by removing it from the context and introducing a function space. Function application combines a function and argument into a term of the result type.

This method of representing STLC terms has two very important benefits:

\begin{itemize}
  \item The terms are well-typed \emph{by construction}. In other words, it is impossible to construct an ill-typed stlc term using this data type.
  \item The terms are well-scoped \emph{by construction}. Free variables are explicitly represented in the typing context. A term with an empty context is guaranteed to contain no free variables.
\end{itemize}

Note also that we do not specify a semantic interpretation for the simply typed lambda calculus and no typing language is specified. This is done intentionally to show that the correctness of |(TTS(stlc))| is independent of the semantics of the simply typed lambda calculus and independent of the typing language. The only restriction on the semantics is that it allows $\beta\eta$-convertibility as defined in section~\ref{subsec:equality}.

\subsection{Manipulating and constructing terms} 
The simply typed lambda calculus comes equipped with a set of functions to construct, and, most importantly, evaluate terms.
\paragraph{Context weakening}
When constructing STLC terms the need arises to introduce fresh variables. Creating room in a typing context for a variable is simple, but the typing context of a term can not be changed at will. A function is needed which changes a term to accept an extra free variable in the context.

Extending a typing context is done with help of the converse function, removal of a variable from the context:

%include ../proof/STLC/Variable/Operations/Subtract.lagda

Using this function it is possible to express how a term \emph{without} a certain variable, can be turned into a term \emph{with} that variable. This is done by the following two functions:

%include ../proof/STLC/Variable/Operations/Weaken.lagda
%include ../proof/STLC/Term/Operations/Weaken.lagda

This formulation gives the flexibility to introduce a free variable at any position in the context.

%include ../proof/STLC/Term/Operations/Simultaneous/Base.lagda

The function |up| shows how a simultaneous substitution can be used to lift a closed term into an arbitrary context.

%include ../proof/STLC/Term/Operations/Up.lagda

%include ../proof/STLC/Term/Operations/Close.lagda

\paragraph{Variable construction}
Variable indices are constructed in the sequential way of Peano numberings. While this simple representation is useful for defining functions and reasoning with indices, it is not very convenient to write variables as sequences of constructors when constructing terms. The helper function |i| makes this process a bit simpler by injecting a natural number into a stlc variable in the free value context.

%include ../proof/STLC/Variable/Inject.lagda

This only works as long as the natural number is within the bounds of the context. This is checked by an inferred predicate in the function |i|. If this predicate holds, a bounded (finite) number can be constructed using |#|, which can then be turned into a variable index using |i'|.

Term construction is facilitated by the function |v|. Variables can now be written as normal numbers:

%include ../proof/STLC/Term/Inject.lagda

Combined with Agda's mix-fix syntax, this yields a relatively clutter-free method of constructing stlc terms:

%include ../proof/STLC/Prelude/Base.lagda

\subsection{Equality}
\label{subsec:equality}
%include ../proof/STLC/Term/Convertibility.lagda

\section{Formalization of \texorpdfstring{|(TTS(stlc))|}{TTS stlc}}

\paragraph{Typing Functor}
%include ../proof/TTS/Functor/Base.lagda

\paragraph{Functor Context}

%include ../proof/TTS/Context/Base.lagda

%include ../proof/TTS/Judgement/Base.lagda

\paragraph{Transformation rules}

There is a bit of room in the design space as to how represent transformation rules. In this version of the type and transform system a simple dictionary of transformable terms is used. Chapter~\ref{chap:extensions} discusses more possibilities for extension.

%include ../proof/TTS/Rules/Base.lagda

The |Rules| datatype is list of transformation terms. A |Rule| indexes a rule in this list. Note that only closed terms can be transformed using this formulation, this makes the transformations context-insensitive.

\section{Properties}
We will now mechanically show that the defined system adheres to the desired transformation properties of Section~\ref{sec:tts}. This proof is follows the same structure as the 'pen-and-paper' proof from Chapter~\ref{chap:proof} and relies on the Curry-Howard correspondence for its validity.

\paragraph{Curry-Howard Correspondence} The Curry Howard correspondence is the notion that there exists a direct connection between types in a programming language and propositions in classical, predicate and intuitionistic logic. This correspondence makes it possible to construct proofs as programs: providing an implementation program for a given type corresponds to proving that same logical property. According to the Curry-Howard correspondence, implication in logic has a direct relation to function space in programming languages, and universal quantification is related to dependent function space. Sum types and product types have a direct relation to disjunction and conjunction. In this way the Curry-Howard correspondence makes it possible to mechanically prove logical properties in a programming language, a feature that is put to good use in this section.

\subsection{Typing property}
The TTS typing property does not need any further proving but is inherent in the construction of the whole system. Terms are type-correct by construction using the well-typed De Bruijn indices and the transformation relation is indexed by two terms which derive a valid type from the typing functor. 

\subsection{Identity transformation} As a bare minimum, all transformation systems should allow the identity transformation to be productive. The following function shows this by showing that a valid transformation derivation exists for any term in the simply typed lambda calculus:

%include ../proof/TTS/Judgement/Properties.lagda

The typing functor and functor context of the identity transformation are the lifted version of the base type and context. The function |! ↑φ-≡Γ , ↑Φ-≡τ >⊢ e| shows Agda that the interpretation of a lifted type, is equal to the base type.

This shows clearly how implication in logic in connected to function space in a programming language. The statement: the existence of a valid term implies the existence of a transformation for that term, is transformed into showing that a function exists which constructs a transformation out of a term. 

\subsection{Semantic equivalence}
The Agda formalization of the equivalence proof strictly follows the proof structure as described in Chapter~\ref{chap:proof}. The first challenge is to find a suitable Agda representation for the logical relation.

\paragraph{Logical relation} To construct the logical relation we can make good use of dependent types: the relation constructs a different type for different Functor constructs. For base types it constructs a $\beta\eta$ equivalence and for function space it constructs an implication in the form of a normal Agda function.

%include ../proof/TTS/Relation/Base.lagda

%include ../proof/TTS/Relation/Properties.lagda

\paragraph{Relating environments} Semantic equivalence is proven 'under related closing environments'. The fact that two closing environments are related is expressed by the following inductive datatype.

%include ../proof/TTS/Relation/Env.lagda

|Rel↓| is indexed by the closing environments it relates. For each two respective terms in the environment a witness |w| is evidence of the fact that both terms are related.

\paragraph{Relating transformation rules} A type and transform transformation is only semantics preserving if the transformation rules preserve the equivalence between the types. This is done by showing that transformed terms are members of the logical relation, and is witnessed by the following construction:

%include ../proof/TTS/Rules/Proof.lagda

%include ../proof/TTS/Properties.lagda

\section{Monoid Transformation}
Because the object language used for mechanically proving |(TTS(stlc))| is rather simple, it is not possible to express Hughes' strings transformation in this framework. However, it is possible to prove a more general transformation of which Hughes' strings is an instantiation: the monoid transformation.

A monoid is a mathematical structure consisting of a type |S| and a binary operation |mplus :: S -> S -> S| and an identity |mzero :: S|, which adhere to the following laws:

> Associativity:  forall a b c. a `mplus` (b `mplus` c) `beq` (a `mplus` b) `mplus` c 
> Identity:       forall a. a `mplus` mzero `beq` mzero `mplus` a `beq` a

It is not difficult to see that |(++)| and |""| form a monoid for |String|s. We can construct a transformation for monoids which will make sure that all applications of the monoid are \emph{right-associative}, exactly what is being done in Hughes' string transformation.

%include ../proof/TTS/Monoid.lagda
