Program transformation is a central aspect of computer science, most importantly in the area of compiler construction. One expects from a compiler to transform human readable code into highly optimized machine code, while maintaining the expected behaviour of the program. During compilation, a compiler makes use of a wide range of program transformations to reach this goal. A program is simplified, variables are renamed and optimizations are applied while the program may be transformed into one or multiple intermediate languages.

\noindent Closely related areas in which program transformations play a role are program refactoring and program migration. Program transformations for refactoring and migration resemble those for compilation in that the behaviour of the resulting program should remain unchanged, but the intention of the transformations are different: Refactoring is done to make a program better readable for humans and migration is done to adapt a program to a changed environment. 

\paragraph{Program transformations}
A program transformation works by inspecting and manipulating the terms of a language to generate the desired result. However, programming languages such as Haskell or Java do not only consist of terms, but of types as well. Designing program transformations for such languages leaves the designer with a choice: either throw away the typing information and apply transformations to untyped terms, or somehow leave the types of the terms in tact during transformation. Throwing away the typing information is sometimes unavoidable, for example when transforming typed Java to untyped assembler code. However, the transformations used for optimizing, refactoring and migration usually produce terms in the same language as their input language. For such transformations the choice between typed and untyped transformation is more difficult. Doing an untyped transformation gives a lot of flexibility, but can more easily result in untypeable terms. Furthermore, the types of a language are also a source of information during transformation, it would be a waste to throw that away! 

For transformations on typed languages, on the other hand, the types themselves can be restrictive. One possibility is to leave the types of the source program in tact during transformation and only substitute equally typed terms. This works, but there is a class of transformations which require changes in the types next to changes in the terms. For example the following transformation, which replaces all occurrences of integral numbers by floating point numbers to reduce the rounding errors in a program:

\begin{minipage}[t]{0.48\textwidth}
> percent :: Int -> Int -> Int
> percent v v' = 100 * (v `div` v')
\end{minipage}
\begin{minipage}[t]{0.48\textwidth}
> percent :: Float -> Float -> Float
> percent v v' = 100 * (v / v')
\end{minipage}

\noindent Such a transformation requires a transformation of both the terms and the types. The types are changed from |Int|s to |Float|s, and the |`div`| operator is replaced by |/|. In recent years several of these type-changing program transformations have been developed, such as the worker/wrapper transformation by Gill and Hutton~\cite{gill09} or a continuation passing style transformation by Ahmed and Blume~\cite{ahmed11}. They both show that their transformations are equivalence preserving and type-preserving, two crucial properties for typed program transformations.

\paragraph{Transformation systems}
Creating such a program transformation is time-consuming and error-prone. It is time-consuming because a transformation has to either be built into an existing compiler, which are complicated pieces of software to work in, or one has to create a custom infrastructure to process terms of the language, which means dealing with detailed implementation issues. Because modern programming languages have many constructs which interact in many subtle ways, an error is easily made. Thus it is also good practice to provide a proof of the fact that a program transformation works as expected. This is especially important because program transformations are used in the critical parts of software systems. An error in a compiler can cause a lot of trouble. However, proving a program transformation correct is not easy and again time-consuming.

To counter these issues, the natural way to go is looking for possible abstractions. Instead of developing individual program transformations, look for parts that can be generalized and develop a generic transformation system in which transformations can be constructed. This makes developing individual transformations faster and easier, resulting in less errors.

\section{Related work}
Several such systems for creating type-aware program transformation have already been developed and implemented in various forms.

\begin{itemize}
  \item The Haskel GHC compiler allows user-defined transformation rules to transform terms, such as the following for map fusion:

> {-# RULES "map/map"    forall f g xs.  map f (map g xs) = map (f . g) xs #-} 

These rewrite rules are used by the compiler to simplify and optimize during compilation. The rules are type-checked using the internal type checker, which quickly catches typos and simple errors. Although the individual rules cannot change the types in a program themselves, combinations of these rules can have much the same effect. This is more thoroughly discussed in Section~\ref{sec:fusion}

  \item Cunha and Visser~\cite{cunha07}~\cite{cunha06} developed a framework for type-changing program transformation as an EDSL in Haskell. Their system works on a point-free representation of terms to avoid having to deal with binders. 

  \item Recently Erwig and Ren~\cite{erwig07} proposed a generic transformation system for type-changing program transformation. In their approach they define an update calculus for program updates which can deal with both type-changes and scoping changes. They show that updates performed by their generic transformation system will result in well-typed programs and that the semantics between the source and result programs are preserved. 
\end{itemize}

\section{Motivation}
Although all these systems facilitate type changes in their own way, none of these systems are suitable for program-wide transformation of types, which is a very real use-case for both program optimization and migration. We call such transformations \emph{type-driven}: transformations in which the ultimate goal is to replace the types in a program. In such a transformation the terms are only changed to make a program work with a new type: term substitution is not a driving factor. We already introduced the transformation of integers to floats as a use-case for a type-driven transformation, but there are many more use-cases:

\begin{itemize}
  \item[\textbf{Migration}] A situation when program-wide modification of types is desired is when migrating between libraries. In Haskell this could be migrating a program which uses |Text| as a representation for character data, to a representation using |ByteString|s. This means changing the |Text| type inside the program as much as possible, and replacing the functions that work on |Text| by functions that work on |ByteString|s. A similar migration occurs when moving between parsing libraries or when upgrading to a new version of a package.

This use-case was the primary motivation for the work of Erwig and Ren. However, their system has a rather ad-hoc way of specifying rules and type changes were very local, not in a program-wide manner.

  \item[\textbf{Optimization}] Another use-case for type-changing program transformations is when the representation of a datatype is changed for optimization purposes. Hughes' strings transformation~\cite{hughes86} and the Stream fusion~\cite{coutts07}~\cite{coutts07b} transformation are prominent examples of this and will be discussed in more detail in Section~\ref{sec:examples}.

  \item[\textbf{Refactoring}] Sometimes it is desired  to change the representation of a datatype because this is more suitable for the programmer. For example, a point in space may be represented by its cartesian coordinates or by polar coordinates. When a user wants to switch between these representations, a transformation could be created to change the representation, and the way in which the program calculates with these representations.
\end{itemize}

Note that in most of these examples the same result could have been achieved by changing the underlying representation of a datatype instead of changing the program. However, this is not possible when the representation of a type is managed externally, for example when transforming base types or types which are part of a standard library. In these cases the only solution is to change the types in a program.

Also, when one wants to replace a type in a program, it is not always possible to find a suitable term-level replacement for all functions. In this case it is not possible to do a program-wide replacement of a type. For example in the case of the integer to floating point transformations, there is no floating point alternative for bit-shifting an |Int| representation. Thus there is no alternative but to keep the type unchanged and convert the floating point to an integer.

\begin{minipage}[t]{0.48\textwidth}
> magic :: Int -> Int -> Int
> magic a b = a .|. xor b
\end{minipage}
\begin{minipage}[t]{0.48\textwidth}
> magic :: Float -> Float -> Float
> magic a b = round a .|. xor (round b)
\end{minipage}

It is also possible that a type is not fully abstract and it can be inspected using pattern matching. In this case the internals of a type are exposed and one does not get around keeping the original type in tact.

Situations like these make it beneficial to have a type-changing transformation system which works directly on program representations and which tries to replace a type as much as possible, but can locally keep the original types in tact.

\section{Contributions}
This work introduces a generic formal system for such type-changing program transformations, which we call type-and-transform systems, TTS for short. This system is intended to be a basis for type-changing program-wide transformations and has the following features:

\begin{itemize}
  \item[\textbf{STLC}] The transformation system is designed for languages based on the simply typed lambda calculus. The core transformations are purely based on STLC, extensions are later discussed.

  \item[\textbf{Generic}] The system is generic in the types and terms that are transformed. It can be parametrized with specific type and term transformations to obtain a specific program transformation. The type and transform system is also independent of the interpretation of the underlying type language.

  \item[\textbf{Proven}] The system is proven to allow only transformations which yield type correct programs and which yield a semantically equivalent program after transformation. This claim is proven using logical relations and mechanically verified in the dependently type programming language Agda~\cite{norell07}, thus contributing to the POPLmark challenge~\cite{poplmark} of verified metatheory in programming languages.
\end{itemize}

Note that this system does not specify how the transformation system is implemented. The |TTS| system specifies the typing rules for type-changing program transformations, not how these transformations are actually performed. Section ~\ref{sec:performing} discusses possibilities for implementation.

\section{Overview}
This section gives an overview of the upcoming chapters.

Chapter~\ref{chap:tts} introduces the general concepts and construction of the |TTS| system. First more extensive motivating examples of type-changing program transformations are introduced in the first two sections. Consequently the basic type and transform system for the simply typed lambda calculus is presented, followed by an example application of the Hughes' strings example in Section~\ref{sec:hughes-transform}. The last section will briefly discuss the possibilities and problems when implementing an actual transformations system.

Chapter~\ref{chap:proof} establishes the core properties of the type and transform system. Section~\ref{sec:typing} and Section~\ref{sec:productivity} establish the type soundness and productivity of the type and transform system. Section~\ref{sec:semantics} introduces logical relations and uses these to prove the semantic correctness of program transformations. The last two section discuss some of the theoretical background of the transformation system.

Chapter~\ref{chap:mechanical} discusses the formalization of the type and transform system in the programming language Agda in the first two sections and shows how the transformation system is mechanically proven correct in section~\ref{sec:mechanical-properties}. Lastly an example transformation will be shown.

In Chapter~\ref{chap:extensions} possible extensions of the type and transform system are discussed, to make the system ready for real-world languages. The last two chapter discuss future work and conclude.

