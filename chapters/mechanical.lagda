%include ../formatting/agda.fmt

Proving properties about the programs we write increases our trust in the reliability of our software. Although a pen-and-paper proof usually suffices to prove properties, it is still possible to make errors. In recent years it has become more common to prove parts of software systems with the use of theorem provers. To take this one step further, the POPLmark~\cite{poplmark} challenge has set its goal to mechanically verify all meta-theory of programming languages.

In this light, we have verified the |(TTS(stlc))| transformation system in the dependently type programming language Agda~\cite{norell07}. Agda is a programming language which can be used for theorem proving and is based on constructive mathematics. We have chosen Agda as proof-assistant because it supports universe polymorphism, clean syntax through the use of mixfix operators and parametrized modules.

This chapter will give an overview of how the transformation system is represented in Agda and how the transformation properties are mechanically verified. The proof relies on the validity of the Curry-Howard correspondence, which will be introduced in Section~\ref{sec:mechanical-properties}. The source code can be found on GitHub~\cite{source} for the interested reader.

\section{STLC Object Language}

Fundamental to a mechanical formalization of the TTS system is the representation of the object language, STLC. STLC can be represented in multiple ways, as described in~\cite{keuchel11}. The essential choice is between a Higher Order Abstract Syntax and a de Bruijn representation, among others. Although HOAS terms can be constructed in Agda, Agda is not strong enough to reason about semantic equivalence of HOAS terms, unlike other languages such as Twelf~\cite{schurmann08}. The representation chosen here is a first-order representation using well-typed de Bruijn indices as found in Keller and Altenkirch~\cite{keller10}. A first-order formulation is mandatory because it allows full inductive reasoning over terms and types in the object language and thus reasoning about the semantics. Formulating using well-typed de Bruijn indices is useful because it asserts important properties about the terms by construction.

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

\subsection{Manipulating and Constructing Terms} 
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

There is a bit of room in the design space as to how represent transformation rules. In this version of the type-and-transform system a simple dictionary of transformable terms is used.

%include ../proof/TTS/Rules/Base.lagda

The |Rules| datatype is a list of transformation terms. A |Rule| indexes a rule in this list. Note that only closed terms can be transformed using this formulation, this makes the transformations context-insensitive.

\section{Properties}
\label{sec:mechanical-properties}
We will now mechanically show that the defined system adheres to the desired transformation properties of Section~\ref{sec:tts}. This proof follows the same structure as the 'pen-and-paper' proof from Chapter~\ref{chap:proof} and relies on the Curry-Howard correspondence for its validity.

\paragraph{Curry-Howard Correspondence} The Curry Howard correspondence is the notion that there exists a direct connection between types in a programming language and propositions in classical, predicate and intuitionistic logic. This correspondence makes it possible to construct proofs as programs: providing an implementation program for a given type corresponds to proving the corresponding logical property. According to the Curry-Howard correspondence, implication in logic has a direct relation to function space in programming languages, and universal quantification is related to dependent function space. Sum types and product types have a direct relation to disjunction and conjunction. In this way the Curry-Howard correspondence makes it possible to mechanically prove logical properties in a programming language, a feature that is put to good use in this section.

\subsection{Typing Property}
The TTS typing property does not need any further proving but is inherent in the construction of the whole system. Terms are type-correct by construction using the well-typed De Bruijn indices and the transformation relation is indexed by two terms which derive a valid type from the typing functor. 

\subsection{Identity Transformation} As a bare minimum, all transformation systems should allow the identity transformation to be productive. The following function shows this by showing that a valid transformation derivation exists for any term in the simply typed lambda calculus:

%include ../proof/TTS/Judgement/Properties.lagda

The typing functor and functor context of the identity transformation are the lifted version of the base type and context.

This shows clearly how implication in logic is connected to function space in a programming language. The statement: the existence of a valid term implies the existence of a transformation for that term, is transformed into showing that a function exists which constructs a transformation out of a term. 

\subsection{Semantic Equivalence}
The Agda formalization of the equivalence proof strictly follows the proof structure as described in Chapter~\ref{chap:proof}. The first challenge is to find a suitable Agda representation for the logical relation. The representation used here was inspired by the work of Swierstra~\cite{swierstra12}, who uses a unary logical relation to prove termination of the simply typed lambda calculus in Agda.

\paragraph{Logical relation} To construct the logical relation we can make good use of dependent types: the relation constructs a different type for the different |Functor| constructors. For base types it constructs a $\beta\eta$ equivalence and for function space it constructs an implication in the form of a normal Agda function.

%include ../proof/TTS/Relation/Base.lagda

%include ../proof/TTS/Relation/Properties.lagda

\paragraph{Relating environments} Semantic equivalence is proven 'under related closing environments'. The fact that two closing environments are related is expressed by the following inductive datatype.

%include ../proof/TTS/Relation/Env.lagda

|Rel↓| is indexed by the closing environments it relates. For each two respective terms in the environment a witness |w| is evidence of the fact that both terms are related.

\paragraph{Relating transformation rules} A type-and-transform transformation is only semantics preserving if the additional transformation rules preserve the transformation equivalence property. This is witnessed by the following construction, which establishes that each transformation rule in a rule set preserves the logical relation.

%include ../proof/TTS/Rules/Proof.lagda

\paragraph{Equivalence proof}
We can now give give a formal proof of the Equivalence transformation property for |(TTS(stlc))|. The proofs in this paragraph are slightly simplified by removing some of the book-keeping which is typical of proofs in intensional type theory. In intensional type theory every commutation between operators or equivalence has to be explicitly applied. The complete proofs can be found in the sources.

%include ../proof/TTS/Properties.lagda

\section{Monoid Transformation}
\label{sec:monoid}
Because the object language used for mechanically proving |(TTS(stlc))| does not specify how types can be inhibited, it is not possible to express Hughes' strings transformation in this framework. However, it is possible to prove a more general transformation of which Hughes' strings is an instantiation: the monoid transformation.

A monoid is a mathematical structure consisting of a type |S| and a binary operation |mplus :: S -> S -> S| and an identity |mzero :: S|, which adhere to the following laws:

> Associativity:  forall a b c. a `mplus` (b `mplus` c) `beq` (a `mplus` b) `mplus` c 
> Identity:       forall a. a `mplus` mzero `beq` mzero `mplus` a `beq` a

It is not difficult to see that |(++)| and |""| form a monoid for |String|s. We can construct a transformation for monoids which will make sure that all applications of the |mplus| function are \emph{right-associative}, exactly what is being done in Hughes' string transformation.

%include ../proof/TTS/Monoid.lagda

\newpage

\section{Discussion}

\paragraph{Extensionality}
The equivalence proof shows that the source and result term from a complete type-and-transform deduction are $\beta\eta$-equivalent \emph{for all possible substitutions}. Earlier we have seen that the simply typed lambda calculus is extensional: if two terms are equivalent for all possible inputs, we can treat those two terms as equal. Thus we should not only be able to deduce that the terms are equal 'up to substitution', but we should be able to deduce a direct equivalence:

> strengthen  : ∀ {Γ n} → (e e' : Γ ⊢ C n) → (s : Γ ↓) 
>             → close e s βη-≡ close e' s → e βη-≡ e'

Although this is a valid statement, it is not possible to prove this directly Agda. Agda does not support a general extensionality lemma, and thus we can not simply deduce the equivalence, although it is correct in this particular case of the simply typed lambda calculus.

\paragraph{Structural Logical Relations}
One way out of this would be to construct a separate, more restrictive logic in which extensionality does hold. This is the approach taken by Schürmann and Sarnat~\cite{schurmann08}. They use logical relations to prove properties about the simply typed lambda lambda calculus in Twelf. To overcome the limits of Twelf's logic they express the logical relation in a \emph{separate logic} defined within Twelf. This separate logic is carefully constructed to hold properties which are not true in Twelf in general. They call this approach structural logical relations.

This same approach can be taken here. Instead of expressing the logical in Agda itself, it can be expressed in a stronger (limited) logic defined \emph{within} Agda, which preserves extensionality. 

\paragraph{Extended types}
This approach may also be used prove or disprove a bit more liberal version of the type-and-transform system. We strongly suspect that the transformation equivalence property does not only hold for terms with \emph{base types} but for hole-free types in general, including function types. However, the logical relation uses Agda's function space to relate function types and it is not possible to eliminate function space without an argument in a language which has no extensionality lemma. The approach of Structural logical relations might be a solution to this.
