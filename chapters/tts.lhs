\section{Motivating Examples}

%include ../formatting/haskell.fmt

\subsection{Hughes' strings}
One example of a type-changing program transformation is known as Hughes' lists ~\cite{hughes86}. In his work, Hughes presents a method which reduces the computational overhead induced by the naive implementation of string concatenation. Hughes' method does not only work for strings, but for lists in general, but in this explanation we will keep to strings for simplicity. To see how this works, first consider the standard implementation of string concatenation:

> infixr 5 ++
> (++) :: String -> String -> String
> []       ++ ys = ys
> (x: xs)  ++ ys = x: xs ++ ys

The running time of this function is dependent on the size of its first argument. Now let us analyze what calculations are being performed when executing the following examples.

> s1, s2, s3, s4 :: [Char]
> s1 = "aap" ++ ("noot" ++ "mies")
> s2 = ("aap" ++ "noot") ++ "mies"
> s3 = "aap" ++ "noot" ++ "mies"
> s4 = (\x -> x ++ "mies") ("aap" ++ "noot")

In the first example |"noot"| is traversed to create |"nootmies"|, and consecutively |"aap"| is traversed to create |"aapnootmies"|. The second example is almost identical, but first |"aapnoot"| is constructed by traversing |"aap"| and then |"aapnootmies"| is constructed after traversing |"aapnoot"|. Thus |"aap"| is traversed twice, a gross inefficiency! To partly counter this problem, |(++)| has been made right-associative, such that the third example produces the most optimal result. However, there are still many cases in which concatenation does not work optimal, as in the fourth example.

The Hughes' lists transformation solves this by treating string not as normal string (|String|) but as functions over strings (|String -> String|). Strings now become continuations of strings, where the continuation represents an unfinished string, for which the tail still has to be filled in. Strings and Hughes' strings can be transformed into each other by the functions |rep| and |abs|.

> (rep_(ss)) :: String -> (String -> String)
> (rep_(ss)) ls = (ls ++)
> 
> (abs_(ss)) :: (String -> String) -> String
> (abs_(ss)) c = c []

The speedup comes from the fact that, instead of normal concatenation, we can use function composition to concatenate two Hughes' strings. 

> s1, s2, s3, s4 :: String
> s1 = (abs_(ss)) $ (rep_(ss)) "aap" `comp` ((rep_(ss)) "noot" `comp` (rep_(ss)) "mies")
> s2 = (abs_(ss)) $ ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot") `comp` (rep_(ss)) "mies"
> s3 = (abs_(ss)) $ (rep_(ss)) "aap" `comp`  (rep_(ss)) "noot" `comp` (rep_(ss)) "mies"
> s4 = (abs_(ss)) $ (\x -> x `comp` (rep_(ss)) "mies") ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot")

All examples now have the same, optimal running time because the continuation technique avoids building intermediate results: each string is only traversed at most once. Additionally, where the speed of normal concatenation depends on the size of its first argument, function composition has a constant running time.

\subsection{Stream fusion}
Another example of a type-changing program transformation is stream fusion, as found in Coutts et al.~\cite{coutts07, coutts07b}. The goal of stream fusion is the same as Hughes' lists: optimizing operations on lists. Stream fusion does this using a technique called deforestation, which reduces the number of intermediate results constructed when doing operations on lists. Consider the following example:

> op :: [a] -> [a]
> op = map f `comp` filter c `comp` map g

When this example is compiled without optimization, an intermediate result will be constructed at the position of each composition. Modern compilers such as GHC can partly optimize this kind of overhead away, but not for all cases. A better solution is to use streams instead of lists. Streams are defined as follows:

> data Step s a =
>     Done
>  |  Yield a s
>  |  Skip s
> 
> data Stream a = some s. Stream { step :: s -> Step s a, seed :: s }

Streams do not represent lists directly, but store a seed and a function. This function can be used to obtain a new item from the list and a modified seed (|Yield|). When the list is empty the function returns |Done|. |Skip| is returned when only the seed is modified. This becomes more clear when looking at the function which converts a stream into a list:

> (abs_(fs)) :: Stream a -> [a]
> (abs_(fs)) stream = extract $ seed stream
>   where
>     extract seed' =
>        case step stream seed' of
>          Done             -> []
>          Skip    newseed  -> extract newseed
>          Yield x newseed  -> x : extract newseed

Conversely we can construct a stream from a list:

> (rep_(fs)) :: [a] -> Stream a
> (rep_(fs)) ls = Stream next ls
>   where
>     next []     = Done
>     next (x:xs) = Yield x xs

Here the list becomes the seed and the step function produces an item from the list at each step.

Many operations on lists can now be implemented by modifying the |step| function instead of traversing the entire stream. In this way intermediate constructions are avoided. An example is the map function:

> mapS :: (a -> b) -> Stream a -> Stream b
> mapS f stream = Stream step' (seed stream)
>     step' seed' =
>       case step stream seed' of
>           Done             -> Done
>           Skip newseed     -> Skip newseed
>           Yield a newseed  -> Yield (f a) newseed

Note that the |mapS| function is not recursive. This is what avoids the intermediate result from being constructed. We can now construct an optimized version of our example:

> op :: [a] -> [a]
> op = (abs_(fs)) `comp` mapS f `comp` filterS c `comp` mapS g `comp` (rep_(fs))

The only function constructing a list is |abs|, all other operations are 'fused' together.

\section{Type and Transform Systems}
\label{sec:TTS}

Looking closely at the previous two examples, we can see a transformation pattern emerge. In both examples a single type is changed into another, more optimized type. All functions on the original type are replaced by functions on the optimized type, while maintaining the same overall semantics. The functions |rep| and |abs| are used to perform conversions between both types.

Type and transform systems are a formalization of this transformation pattern. In this section, the core concepts of this formalization will be introduced.

\paragraph{TTS properties} A type and transform system (TTS) transforms a program which, when a transformation is successful, guarantees the following TTS properties:

\begin{enumerate}
  \item\label{prop:types} The source and result program have equal types
  \item\label{prop:semantics} The source and result program are semantically equivalent
\end{enumerate}

There are some important restrictions and liberties implied by these two properties that should be noted here. First off, property~\ref{prop:types} implies that the source program has to be well-typed to be transformed, and that the result program will be well-typed. Also, while property~\ref{prop:types} restricts transformations to preserve the type of the entire program, it does not restrict type changes to subterms of the program. In the same manner property~\ref{prop:semantics} requires only the complete programs to be semantically equivalent but says nothing about the semantics of its subterms. This is best illustrated with a few examples of Hughes' strings transformations:

\begin{figure}[H]
\begin{align}
|"aap"| &|`rw`| |"aap"| \label{eq:trivial}\\
|"app"| &|`nrw`| |42| \label{eq:type-wrong}\\
|"app"| &|`nrw`| |"noot"| \label{eq:constant-wrong}\\
|upper "aap"| &|`nrw`| |(rep_(ss)) ((abs_(ss)) upper) "aap"| \label{eq:upper-wrong}\\
|"app" ++ "noot"| &|`nrw`| |(rep_(ss)) "aap" `comp` (rep_(ss)) "noot"| \label{eq:incomplete}\\
|"aap" ++ "noot"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot")| \label{eq:complete}\\
|(\ x. x ++ "noot") "aap"| &|`nrw`| |(abs_(ss)) (\ x. (rep_(ss)) x `comp` (rep_(ss)) "noot") "aap"| \label{eq:ab-wrong}\\
|(\ x. x ++ "noot") "aap"| &|`rw`| |(abs_(ss)) ((\ x. x `comp` (rep_(ss)) "noot") ((rep_(ss)) "aap"))| \label{eq:ab-right}\\
|"aap"| &|`rw`| |(abs_(ss)) ((rep_(ss)) "aap"))| \label{eq:retract-right}
\end{align}
\caption{Transformation examples}
\label{fig:example-transform}
\end{figure}

The |`rw`| symbol is used to denote a valid transformation from some program to a resulting program, |`nrw`| represents transformations which do not adhere to the TTS transformation properties. The first two transformations are valid and invalid for obvious reasons. Example~\ref{eq:constant-wrong} and ~\ref{eq:upper-wrong} are examples of when the types of a transformation are valid, but the semantics of the program have changed. Example~\ref{eq:incomplete} does not preserve the typing property and is thus not valid, the next example shows how this could become valid. Examples ~\ref{eq:ab-wrong} and ~\ref{eq:ab-right} are another example of wrong and right placement of |(rep_(ss))| and |(abs_(ss))|. The last example~\ref{eq:retract-right} is correct and illustrates that in general the |(abs_(ss))| and |(rep_(ss))| function from Hughes' string transformation have the property that |abs `comp` (rep_(ss)) == id|. This property is key to the construction of the TTS system and will be elaborated upon in the next paragraph.

\paragraph{Restricted type changes}
Looking at the stream fusion and Hughes' strings examples we see that in both cases only one type is being changed. For Hughes' strings transformation, strings are changed to string continuations and with stream fusion lists are changed to streams. We will restrict the TTS system to only changing one base type in the source program to one different type in the resulting program. The type within the source program is denoted by |tyA|, the type in the result program by |tyR|. These source and result types are required to form a retract, written as |tyA `ret` tyR|. Two types form a retract when there exists a pair of functions, |rep :: tyA -> tyR| and |abs :: tyR -> tyA|, for which |abs| is the left inverse of |rep|, meaning that |abs `comp` rep == id|. Both Hughes' strings and the stream fusion functions |rep| and |abs| have this property.

\paragraph{Object Language}
A TTS can be built for many different programming languages. The language a TTS is designed for is called the object language. However, not every language is suitable as object language. The first TTS property requires the object language to be strongly typed. Also, in order to be able to relate the semantics of the source and result of a transformation, the object language should come with an equivalence relation for the semantics of its terms. 

One of the most simple languages which is suitable as a TTS object language is the simply typed lambda calculus. We will use this language here to further introduce the core concepts of type and transform system, Chapter~\ref{chapter:extra} handles TTS systems for object languages with more advanced features. The terms and types of the simply typed lambda calculus are of the following form:

> e   ::= x | c | e e | \x. e
> ty  ::= T | ty -> ty

As expressions we have variables, constants, application and abstraction. Types can either be base types or function space. Figure~\ref{fig:stlc} gives the well-known typing rules for the simply typed lambda calculus. The type and transform system for the simply typed lambda calculus is called |(TTS(stlc))|.

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

The judgement |env `stlc` e : ty| can be seen as a 3-way relation between types, terms and type environments. The elements of this relation consist of the valid stlc type assignments, and membership to this relation is determined by the typing rules. This relation is the starting point for defining a type and transform system for the simply typed lambda calculus.

\paragraph{The TTS relation}
At the heart of each type and transform system there is a TTS relation. A TTS relation contains the valid transformations between source and result terms, together with the typing information for both these terms. A TTS relation can be systematically derived from the typing relation of the underlying object language. For STLC we derive the following relation:

> envF `stlc` e `rw` e' : tyF

The resemblance with the original STLC typing judgement is obvious. Instead of one term, the relation now embodies two terms, the source and the result term. The |envF| and |tyF| constructions are similar to normal types and contexts, except that they type the source and the result term simultaneously. Any variation in types between the two terms, is expressed in those constructions. We call such a modified type a typing functor and the context a functor context.

\paragraph{Typing functor}
The variation in types in a type and transform system is limited to only changing one base type |tyA| from the source program into a base type |tyR| in the transformation result. The typing functor allows such changes, while maintaining the invariant that both source and result terms are well-typed. The way this is achieved, is by extending the normal types of the object language with an 'hole' construction. This hole will represent the locations at which the types have changed during transformation. For STLC, the typing functor and functor context are defined as follows:

> tyF   := tyI | T | tyF -> tyF
> envF  := empty | envF, x : tyF

Along with the typing functor and context we define a function which turns a functor into a base type of the object language. This is done by filling in the hole type with some type argument. This interpretation function for the typing functor and context are defined as follows:

> (int_(_)(_)) : tyF -> ty -> ty
> (int_(ty)(ty))                      = ty
> (int_(T)(ty))                       = T
> (int_((tyF_(a)) -> (tyF_(r)))(ty))  = (int_((tyF_(a)))(ty)) -> (int_((tyF_(r)))(ty))

> (int_(_)(_)) : envF -> ty -> ty
> (int_(empty)(ty))          = empty
> (int_(envF, a : tyF)(ty))  = (int_(envF)(ty)) , a : (int_(tyF)(ty))

If a typing functor or context contains no holes we call it \textbf{complete}. Note that when a typing functor is complete, it is actually just an ordinary type in the object language. The predicate |pC| is used to decide completeness of a typing functor or context, such that if |tyF| is complete, |pC(tyF)| holds.

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

Note that the functions involved in transformation (|(rep_(ss))|, |(abs_(ss))|, |(++)| and |`comp`|) are not members of the functor context. These transformation terms are not introduced by the context but by separate rules in the TTS. 

These examples also show that not every member of the typing relation is a valid TTS transformation, because, for a transformation to be a valid TTS transformation, the type of the source term has to be identical to the type of the result term. However, the typing relation explicitly allows changes in types. The elements of the typing relation which are also a valid TTS transformations are those for which the functor and functor context are complete. These contain no holes and thus no type changes. An element of the typing relation which has a complete typing functor and functor context is also called complete.

\subsection{A TTS for STLC}
The elements of a TTS relation are defined using inference rules. Figure~\ref{fig:stlcrules} introduces the basic inference rules for |(TTS(stlc))|. The first four rules (|Tr-Con|, |Tr-Var|, |Tr-Lam| and |Tr-App|) are modified versions of the STLC inference rules. An extra result term has been added and types have been changed to functors, just as the TTS relation. These rules do not perform any actual transformation but make sure transformation progresses over parts of the program which do not change. Consequently they are called the propagation rules.

Note that with the introduction of constants in |Tr-Con|, it is only allowed to introduce a constant with a base type, not a functor type. This base type can be treated as a functor type in the conclusion, because a functor type is an extensions of the base types: each base type is also a valid functor type.

The rules |Tr-Rep| and |Tr-Abs| are called the introduction and elimination rules. These rules are used to convert a term of the source type to a term of the result type and back. Introduction using |Tr-Rep| introduces a hole in the typing functor, reflecting that the type of the term has changed at the position of this type. Note that the type |tyA| and the functions |rep| and |abs| may be different for different instantiations of this basic STLC transformation system.

\begin{figure}[t]
\begin{tabular}{l r c l r}
|Tr-Con|
&\inferrule{|c is a constant of type ty|}
           {|envF `stlc` c `rw` c : ty|}
&\quad
&\inferrule{|c is a constant of type ty|}
           {|env `stlc` c : ty|}
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
&\boxed{|envF +- e `rw` e' : tyF|}
&\quad
&\boxed{|G +- e : F|}
\end{tabular}
\caption{Type checking rules for the propagation relation}
\label{fig:stlcrules}
\end{figure}

These rules form the basis for all STLC-based transformation systems. For specific transformations such as Hughes' strings this core is extended with extra rules to perform the required transformations.

\section{A TTS for Hughes' strings}
The Hughes' strings transformation constitutes of three core transformations: converting a string to a string continuation (|rep|), converting a string continuation back to a string (|abs|), and replacing string concatenation with function composition. For the STLC version of the Hughes' strings transformation, the |(TTS(stlc))| base system is instantiated with the parameters specific to Hughes' strings. The source type |tyA| is instantiated to |String|, |tyR| is instantiated to |String -> String| and the functions |rep| and |abs| in the |Tr-Rep| and |Tr-Abs| rules are taken to be the |rep_(ss)| and |abs_(ss)| functions from Hughes' strings. What is left is adding a rule for transforming string concatenation to function composition. This rule looks as follows:

\begin{align*}
&|Tr-Comp|
&\quad
&\inferrule{ }
           {|envF `stlc` (++) `rw` (`comp`) : tyI -> tyI -> tyI|}
\end{align*}

The rule |Tr-Comp| introduces the functor type |tyI -> tyI -> tyI|, reflecting the type changes induced by this transformation. 

\paragraph{Example} Figure~\ref{fig:hughesexample} shows an example derivation for a program transformation. This particular transformation derivation shows that the term |(\x. x ++ "b") "a"| can be transformed to the the term |abs ((\x. x `comp` rep "b") (rep "a"))| using the Hughes' lists transformation system. This example illustrates how both source and result terms are constructed and typed simultaneously when deriving a transformation. The result of the transformation yields a complete element of the TTS relation, and is thus a valid TTS transformation.

%include example.lhs



\section{Performing a transformation}
%Write about Syntax-directed
