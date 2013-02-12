Looking closely at the previous two examples, we can see a transformation pattern emerge. The transformations are \emph{type-directed}: in both examples a single type is changed into another, more optimized type. The term transformations consequently follow the transformation of the types: all functions on the original type are replaced by functions on the optimized type, while maintaining the same overall semantics. In the process of transforming to a new type, the functions |rep| and |abs| have the special role of performing conversions between the original and the new type.

Type and transform systems are a formalization of this transformation pattern. In this section, the core concepts of this formalization will be introduced.

\subsection{Transformation properties}
\label{subsec:properties}
Before developing a transformation system, it useful to formalize some overall properties that we want a transformation system to uphold. Type and transform systems are intended to maintain the following properties for its transformations:

\begin{enumerate}
  \item[\textbf{Sound}      \namedlabel{prop:types}{1}]      The source and result program have equal types
  \item[\textbf{Equivalence}\namedlabel{prop:semantics}{2}]  The source and result program are semantically equivalent
  \item[\textbf{Productive} \namedlabel{prop:productive}{3}] A transformation yields a result for all possible inputs
\end{enumerate}

Note that property the soundness does not exclude changes of types within a program. The complete program after transformation should have the same type as the original, but types may have been changed within the subterms. In other words: the resulting types remain the same, but the \emph{typing derivation} may differ. In the same manner the equivalence property requires only the complete programs to be semantically equivalent but says nothing about the semantics of its sub-terms. This is consistent with the example transformations: Locally the types and terms have been changed, but the overall type and semantics have remained the same.

Furthermore, this implies that the source program has to be well-typed to be eligible for transformation. The transformation should also provably produce a type-correct program as a result.

To get a feeling for what could be a valid transformation, consider the following example transformations:

\begin{figure}[H]
\begin{align}
|"aap"| &|`rw`| |"aap"| \label{eq:trivial}\\
|"aap"| &|`nrw`| |42| \label{eq:type-wrong}\\
|"aap"| &|`nrw`| |"noot"| \label{eq:constant-wrong}\\
|upper "aap"| &|`nrw`| |(rep_(ss)) ((abs_(ss)) upper) "aap"| \label{eq:upper-wrong}\\
|"app" ++ "noot"| &|`nrw`| |(rep_(ss)) "aap" `comp` (rep_(ss)) "noot"| \label{eq:incomplete}\\
|"aap" ++ "noot"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot")| \label{eq:complete}\\
|(\ x. x ++ "noot") "aap"| &|`rw`| |(abs_(ss)) ((\ x. x `comp` (rep_(ss)) "noot") ((rep_(ss)) "aap"))| \label{eq:ab-right}\\
|(\ x. x ++ "noot") "aap"| &|`rw`| |(abs_(ss)) ((\ x. (rep_(ss)) x `comp` (rep_(ss)) "noot") "aap")| \label{eq:ab-right2}\\
|(\ x. x ++ "noot") "aap"| &|`nrw`| |(rep_(ss)) ((abs_(ss)) (\ x.  x ++ "noot")) "aap"| \label{eq:ab-wrong}\\
|"aap"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap"))| \label{eq:retract-right}
\end{align}
\caption{Transformation examples}
\label{fig:example-transform}
\end{figure}

The |`rw`| symbol is used to denote a valid transformation from some program to a resulting program, |`nrw`| represents transformations which do not adhere to the TTS transformation properties. The first two transformations are valid and invalid for obvious reasons. Example~\ref{eq:constant-wrong} and ~\ref{eq:upper-wrong} show transformations in which the types of a transformation are valid, but the semantics of the program have changed. Example~\ref{eq:incomplete} does not preserve the typing property and is thus not valid, the next example shows how this could become valid. Examples ~\ref{eq:ab-right} and ~\ref{eq:ab-right2} show that there can be multiple valid results for the same source program. The next example shows that the wrong placement of |(abs_(ss))| and |(rep_(ss))| can result in a type-correct solution, but with the wrong semantics. I this case, |"noot"| and |"app"| will be reversed! The last example~\ref{eq:retract-right} is correct and illustrates that the |(abs_(ss))| and |(rep_(ss))| function from Hughes' string transformation have the property that |abs `comp` (rep_(ss)) == id|. This property is key to the construction of the TTS system and will be elaborated upon in the next paragraph.

\paragraph{Restricted type changes}
Looking at the stream fusion and Hughes' strings examples we see that in both cases only one type is being changed. For Hughes' strings transformation, strings are changed to string continuations and with stream fusion lists are changed to streams. We will restrict the TTS system to only changing one base type in the source program to one different type in the resulting program. The type within the source program is denoted by |tyA|, the type in the result program by |tyR|. These source and result types are required to form a \emph{retract}, written as |tyA `ret` tyR|. Two types form a retract when there exists a pair of functions, |rep :: tyA -> tyR| and |abs :: tyR -> tyA|, for which |abs| is the left inverse of |rep|, meaning that |abs `comp` rep == id|. Both Hughes' strings and the stream fusion functions |rep| and |abs| have this property.

\subsection{Object Language}
A TTS can be built for many different programming languages. The language a TTS is designed for is called the object language. However, not every language is suitable as object language. To assure the type soundness transformation property, the object language should have a strong type system. Also, in order to be able to relate the semantics of the source and result of a transformation, the object language should come with an equivalence relation for the semantics of its terms.

One of the most simple languages which is suitable as a TTS object language is the simply typed lambda calculus (stlc). This language will be used to further introduce the core concepts of type-and-transform systems. Chapter~\ref{chap:extensions} handles TTS systems for object languages with more advanced features.

The terms and types of the simply typed lambda calculus are of the following form:

> e    ::= x | c | e e | \x. e
> ty   ::= T | ty -> ty
> env  ::= empty | env, x : ty

As expressions we have variables, constants, application and abstraction. Types can either be base types or function space. Figure~\ref{fig:stlc} gives the well-known typing rules for the simply typed lambda calculus. The type-and-transform system for the simply typed lambda calculus is called |(TTS(stlc))|.

\begin{figure}[t]
\begin{align*}
&|Con|
&\quad
&\inferrule{|c is a constant of type T|}
           {|env `stlc` c : T|}
\\
&|Var|
&\quad
&\inferrule{|x : ty `elem` env|}
           {|env `stlc` x : ty|}
\\
&|Lam|
&\quad
&\inferrule{|env, x : (ty_(a)) +- e : (ty_(r))|}
           {|env `stlc` \x. e : (ty_(a)) -> (ty_(r))|}
\\
&|App|
&\quad
&\inferrule{|env `stlc` f : (ty_(a)) -> (ty_(r))| \\\\
            |env `stlc` e : (ty_(a))|}
           {|env `stlc` f e : (ty_(r))|}
\\
&|Judgement|
&\quad
&\boxed{|env `stlc` e : ty|}
\end{align*}
\caption{Typing rules for the simply typed lambda calculus}
\label{fig:stlc}
\end{figure}

The judgement |env `stlc` e : ty| can be seen as a 3-way relation between types, terms and type environments. The elements of this relation consist of the valid stlc type assignments, and membership to this relation is determined by the typing rules. This relation is the starting point for defining a type-and-transform system for the simply typed lambda calculus.

It is not necessary to specify a complete semantics for the simply typed lambda calculus. |(TTS(stlc))| is valid for all semantics which admit $\beta\eta$-convertibility on terms, as will be shown in chapter~\ref{chap:proof}.

\paragraph{The |(TTS(stlc))| relation}
At the heart of each type-and-transform system there is a TTS relation. A TTS relation contains the valid transformations between source and result terms, together with the typing information for both these terms. A TTS relation can be systematically derived from the typing relation of the underlying object language. For STLC we derive the following relation:

> envF `stlc` e `rw` e' : tyF

The resemblance with the original STLC typing judgement is obvious. Instead of one term, the relation now embodies two terms, the source and the result term. The |envF| and |tyF| constructions are similar to normal types and contexts, except that they type the source and the result term simultaneously. Such a modified type is called a \emph{typing functor} and the context is called a \emph{functor context}. Any variation in types between the source and result terms is embodied in the typing functor and functor context.

\paragraph{Typing functor}
The variation in types in |(TTS(stlc))| is limited to only changing one base type |tyA| from the source program into a type |tyR| in the transformation result. The typing functor allows such changes, while maintaining the invariant that both source and result terms are well-typed. The way this is achieved, is by extending the normal types of the object language with an 'hole' construction, represented by a $\iota$. This hole will represent the locations at which the types have changed during transformation. For STLC, the typing functor and functor context are defined as follows:

> tyF   ::= tyI | T | tyF -> tyF
> envF  ::= empty | envF, x : tyF

Along with the typing functor and context we define a function which turns a functor into a base type of the object language. This is done by filling in the hole type with some type argument. This interpretation function for the typing functor and context are defined as follows:

> (int_(tyF)(ty)) : ty
> (int_(tyI)(ty))                   = ty
> (int_(T)(ty))                     = T
> (int_(tyF_(a) -> (tyF_(r)))(ty))  = (int_(tyF_(a))(ty)) -> (int_(tyF_(r))(ty))

> (int_(envF)(ty)) : env
> (int_(empty)(ty))          = empty
> (int_(envF, a : tyF)(ty))  = (int_(envF)(ty)) , a : (int_(tyF)(ty))

The typing functor and context are an extension of normal types. Thus, normal types naturally give rise to a functor, as is shown by the following lifting functions:

> (lift(ty)) : tyF
> (lift(T))                     = T
> (lift( (ty_(a)) -> (ty_(r)) ))  = (lift(tyF_(a))) -> (lift(tyF_(r)))

> (lift(env)) : envF
> (lift(env))           = empty
> (lift(env , a : ty))  = (lift(env)) , a : (lift(ty))

If a typing functor or context contains no holes we call it \emph{complete}. Note that when a typing functor is complete, it is actually just an ordinary type in the object language, lifted to a functor.

We can now construct some well-typed transformation examples for Hughes' strings as members of the TTS relation. The hole type is inserted at places where the type |String| in the source term is replaced by the type |String -> String| in the result term. Thus the hole type reflects a change in types.

\begin{figure}[H]
\begin{align}
|empty `stlc` "aap"| &|`rw`| |"aap"| && |: String|  \notag \\
|empty `stlc` "aap"| &|`rw`| |(rep_(ss)) "aap"| && |: tyI| \notag \\
|empty `stlc` (++)|  &|`rw`| |`comp`| && |: tyI -> tyI -> tyI| \notag \\
|empty `stlc` \x.x ++ "hoi"| &|`rw`| |\x.x `comp` (rep_(ss)) "hoi"| && |: tyI -> tyI| \notag  \\
|empty, x : tyI `stlc` x ++ "hoi"| &|`rw`| |x `comp` (rep_(ss)) "hoi"| && |: tyI| \notag \\
|empty `stlc` "aap" ++ "hoi"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap" `comp` (rep_(ss)) "hoi")| && |: String| \notag \\
|empty `stlc` "aap"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap")| && |: String| \notag
\end{align}
\caption{Transformation examples}
\label{fig:example-holes}
\end{figure}

A member of the |(TTS(stlc))| typing relation is said to be \emph{complete} when it results in a base type and the typing context is \emph{complete}. Because a complete functor type is just a lifted base type, we can write a complete transformation in the following form: |(lift(env)) `stlc` e `rw` e' : T|. Each complete element of the typing relation should preserve the TTS properties. This claim will be shown in chapter~\ref{chap:proof} for |(TTS(stlc))|.

\subsection{A TTS for STLC}
The elements of a TTS relation are defined using inference rules. Figure~\ref{fig:stlcrules} introduces the basic inference rules for |(TTS(stlc))|. The first four rules (|Tr-Con|, |Tr-Var|, |Tr-Lam| and |Tr-App|) are modified versions of the STLC inference rules: an extra result term has been added and types have been changed to functors, just as the TTS relation. These rules do not perform any actual transformation but make sure transformation progresses over parts of the program which do not change. Consequently they are called the propagation rules. The existence of these rules makes that this transformation system adheres to the productivity property: there is always an identity transformation rule.

The rules |Tr-Rep| and |Tr-Abs| are called the introduction and elimination rules. These rules are used to convert a term of the source type to a term of the result type and back. Introduction using |Tr-Rep| introduces a hole in the typing functor, reflecting that the type of the term has changed at the position of this type. Note that the type |tyA|, |tyR| and the functions |rep| and |abs| may be different for different instantiations of this basic STLC transformation system.

\begin{figure}[t]
\begin{tabular}{l r c l r}
|Tr-Con|
&\inferrule{|c is a constant of type T|}
           {|envF `stlc` c `rw` c : T|}
&\quad
&\inferrule{|c is a constant of type T|}
           {|env `stlc` c : T|}
&|Con|
\\
|Tr-Var|
&\inferrule{|x : tyF `elem` envF|}
           {|envF `stlc` x `rw` x : tyF|}
&\quad
&\inferrule{|x : ty `elem` env|}
           {|env `stlc` x : ty|}
&|Var|
\\
|Tr-Lam|
&\inferrule{|envF, x : (tyF_(a)) `stlc` e `rw` e' : (tyF_(r))|}
           {|envF `stlc` \x. e `rw` \x. e' : (tyF_(a)) -> (tyF_(r))|}
&\quad
&\inferrule{|env, x : (ty_(a)) `stlc` e : (ty_(r))|}
           {|env `stlc` \x. e : (ty_(a)) -> (ty_(r))|}
&|Lam|
\\
|Tr-App|
&\inferrule{|envF `stlc` f `rw` f' : (tyF_(a)) -> (tyF_(r))| \\\\
            |envF `stlc` e `rw` e' : (tyF_(a))|}
           {|envF `stlc` f e `rw` f' e' : (tyF_(r))|}
&\quad
&\inferrule{|env `stlc` f : (ty_(a)) -> (ty_(r))| \\\\
            |env `stlc` e : (ty_(a))|}
           {|env `stlc` f e : (ty_(r))|}
&|App|
\\
|Tr-Rep|
&\inferrule{|envF `stlc` e `rw` e' : tyA|}
           {|envF `stlc` e `rw` rep e' : tyI|}
\\
|Tr-Abs|
&\inferrule{|envF `stlc` e `rw` e' : tyI|}
           {|envF `stlc` e `rw` abs e' : tyA|}
\\
|Judgement|
&\boxed{|envF `stlc` e `rw` e' : tyF|}
&\quad
&\boxed{|env `stlc` e : ty|}
\end{tabular}
\caption{Type checking rules for the propagation relation}
\label{fig:stlcrules}
\end{figure}

These rules form the basis for all STLC-based transformation systems. For specific transformations such as Hughes' strings this core is extended with extra rules to perform the required transformations.

\section{A TTS for Hughes' Strings}
\label{sec:hughes-transform}
The Hughes' strings transformation constitutes of three core transformations: converting a |String| to a |String| continuation (|(rep_(ss))|), converting a |String| continuation back to a |String| (|(abs_(ss))|), and replacing |String| concatenation with function composition. For the STLC version of the Hughes' strings transformation, the |(TTS(stlc))| base system is instantiated with the parameters specific to Hughes' strings. The source type |tyA| is instantiated to |String|, |tyR| is instantiated to |String -> String| and the functions |rep| and |abs| in the |Tr-Rep| and |Tr-Abs| rules are taken to be the |rep_(ss)| and |abs_(ss)| functions from Hughes' strings. What is left is adding a rule for transforming string concatenation to function composition. This rule looks as follows:

\begin{align*}
&|Tr-Comp|
&\quad
&\inferrule{| |}
           {|envF `stlc` (++) `rw` (`comp`) : tyI -> tyI -> tyI|}
\end{align*}

The rule |Tr-Comp| introduces the functor type |tyI -> tyI -> tyI|, reflecting the type changes induced by this transformation. The Hughes' strings transformation is abbreviated as |(TTS(ss))|.

\paragraph{Example} Figure~\ref{fig:hughesexample} shows an example derivation for a program transformation. This particular transformation derivation shows that the term |(\x. x ++ "b") "a"| can be transformed to the term |abs ((\x. x `comp` rep "b") (rep "a"))| using the Hughes' lists transformation system. This example illustrates how both source and result terms are constructed and typed simultaneously when deriving a transformation. The result of the transformation yields a complete element of the TTS relation, and is thus a valid TTS transformation.

%include example.lhs

\section{Performing a Transformation}
\label{sec:performing}
In the previous sections a basic transformation system is presented which defines what constitutes a valid transformation for |(TTS(stlc))|. However, this deduction system does not show how to algorithmically perform an actual transformation. For example, the deduction system allows an infinite application of the |rep| and |abs| rule, such as the following:

> e `rw` abs (rep (abs (rep e)))

This is hardly an optimizing program transformation! Even worse, the system allows endless chains of |abs| and |rep| applications, thus allowing infinite deduction trees. The reason that such endless chains can occur is because the rules of |(TTS(stlc))| are not \emph{syntax directed}. In a normal typing derivation for the simply typed lambda calculus, the derivation tree is uniquely determined by the term that is being typed. However, in the |(TTS(stlc))| system this is not the case. Multiple results are possible for the same input.

Thus program transformation becomes a form of proof search: Given an input program, try to find a valid |(TTS(stlc))| derivation. While one can always create an identity transformation (do nothing), this would not result in any improvements. One wants to find a transformation which gives as much optimization as possible, while avoiding unnecessary application of |abs| and |rep|.

How to actually do this is not part of this work, but is part of ongoing research by Sean Leather.