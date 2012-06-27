\section{Motivating Examples}

%include ../formatting/haskell.fmt

\subsection{Hughes' lists}
One example of a type-changing program transformation is known as Hughes' lists ~\cite{hughes86}. In his work, Hughes presents a method which reduces the computational overhead induced by the naive implementation of list concatenation. To see how this works, first consider the following implementation of list concatenation:

> (++) :: [a] -> [a] -> [a]
> []       ++ ys = ys
> (x: xs)  ++ ys = x: xs ++ ys
> infixr 5 ++

The running time of this function is dependent on the size of its first argument. Now let us see what calculations are being performed in the following examples.

> s1, s2, s3, s4 :: [Char]
> s1 = "aap" ++ ("noot" ++ "mies")
> s2 = ("aap" ++ "noot") ++ "mies"
> s3 = "aap" ++ "noot" ++ "mies"
> s4 = (\x -> x ++ "mies") ("aap" ++ "noot")

In the first example |"noot"| is traversed to create |"nootmies"|, and consecutively |"aap"| is traversed to create |"aapnootmies"|. The second example is almost identical, but first |"aapnoot"| is constructed by traversing |"aap"| and then |"aapnootmies"| is constructed after traversing |"aapnoot"|. Thus |"aap"| is traversed twice, a gross inefficiency! To partly counter this problem, |(++)| has been made right-associative, such that the third example produces the most optimal result. However, there are still many cases in which concatenation does not work optimal, as in the fourth example.

The Hughes' list transformation solves this by treating lists not as normal lists(|[a]|) but as functions over lists(|[a] -> [a]|). Lists now become continuations of lists, where the continuation represents an unfinished list, for which the tail still has to be filled in. Lists and Hughes' lists can be transformed into each other by the functions |rep| and |abs|.

> type HughesList a = [a] -> [a]
>
> rep :: [a] -> HughesList a
> rep ls = (ls ++)
> 
> abs :: HughesList a -> [a]
> abs c = c []

The speedup comes from the fact that, instead of normal concatenation, we can use function composition to concatenate two Hughes' lists. 

> s1, s2, s3, s4 :: [Char]
> s1 = abs $ rep "aap" `comp` (rep "noot" `comp` rep "mies")
> s2 = abs $ (rep "aap" `comp` rep "noot") `comp` rep "mies"
> s3 = abs $ rep "aap" `comp`  rep "noot" `comp` rep "mies"
> s4 = abs $ (\x -> x `comp` rep "mies") (rep "aap" `comp` rep "noot")

All examples now have the same, optimal running time because the continuation technique avoids building intermediate results: each list is only traversed at most once. Additionally, where the speed of normal concatenation depends on the size of its first argument, function composition has a constant running time.

\subsection{Stream fusion}
Another example of a type-changing program transformation is stream fusion, as found in Coutts et al.~\cite{coutts07, coutts07b}. The goal of stream fusion is the same as Hughes' lists: optimizing operations on lists. Stream fusion does this using a technique called deforestation, which reduces the number of intermediate results constructed when doing operations on lists. Consider the following example:

> map f `comp` filter c `comp` map g

When this example is compiled without optimization, an intermediate result will be constructed at the position of each composition. Modern compilers such as GHC can partly optimize this kind of overhead away, but not for all cases. A better solution is to use streams instead of lists. Streams are defined as follows:

> data Step s a =
>     Done
>  |  Yield a s
>  |  Skip s
> 
> data Stream a = some s. Stream { step :: s -> Step s a, seed :: s }

Streams do not represent lists directly but store a seed and a function which can be used to obtain a new item from the list and a modified seed (|Yield|). When the list is empty |Done| will be returned and |Skip| will just modify the seed. This becomes more clear when we look at the function which converts a stream into a list:

> abs :: Stream a -> [a]
> abs stream = extract $ seed stream
>   where
>     extract seed' =
>        case step stream seed' of
>          Done             -> []
>          Skip    newseed  -> extract newseed
>          Yield x newseed  -> x : extract newseed

In a similar fashion we can construct a stream from a list:

> rep :: [a] -> Stream a
> rep ls = Stream next ls
>   where
>     next []     = Done
>     next (x:xs) = Yield x xs

Here the list becomes the seed and the step function produces an item from the list at each step.


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


\section{Type and Transform Systems}

Looking closely at the previous two examples, we can see a transformation pattern emerge. In both examples a single type is changed into another, better optimized type. All functions on the original type are replaced by functions on the optimized type, while maintaining the same semantic behaviour. The functions |rep| and |abs| are used to perform conversions between both types.

Type and transform systems are a formalization of this transformation pattern. 


\subsection{Object Language}

\subsection{Typing functor}

\section{An STLC-based transformation system}
A type and transform system (TTS) transforms a program which, when the transformation
is successful, guarantees the following TTS properties:

\begin{itemize}
  \item The source and result program are well-typed
  \item The source and result program are semantically equivalent
\end{itemize}

At the heart of a TTS is the TTS relation. The TTS relation specifies which well-typed source programs can be turned into a well-typed result program, as such:

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

%include ../formatting/rules.fmt

\begin{figure}[t]
\begin{align*}
&|Id|
&\quad
&\inferrule{| |}
           {|G +- x `rw` x : F|}
\\
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
&|I-Rep|
&\quad
&\inferrule{|G +- e `rw` e' : A|}
           {|G +- e `rw` rep e' : Id|}
\\
&|I-Abs|
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

\section{A TTS for Hughes' lists}
With the basic STLC TTS system in place, we can now define TTS system for Hughes' list transformation.


 
\subsection{Example}
%include example.lhs

\section{A TTS for Stream fusion}

