%include ../formatting/haskell.fmt

The goal of a TTS relation is to enforce the TTS properties on a transformation. This chapter is dedicated to showing that this is indeed the case for the base system of |(TTS(stlc))|. The main theorem shown here is formulated as follows:

\begin{thrm}[Complete |(TTS(stlc))| transformations ensure the TTS properties]
\label{thrm:stlc-tts}
For all complete elements |envF `stlc` e `rw` e' : tyF| from the relation |(TTS(stlc))|, the transformation |e `rw` e'| adheres to the TTS properties.
\end{thrm}

This theorem is proven by showing that both TTS properties hold. The first section will show the first TTS property involving typing and type equality, the second section will show the second TTS property: transformation should be semantics preserving. 

\section{|(TTS(stlc))| typing properties}
The first TTS property implies that a TTS transformation should only allow correctly typed source and result programs. In other words, a TTS relation should be sound with respect to the underlying object language. This is formalized in the following way:

\begin{lemma}[|(TTS(stlc))| relation preserves typing]
\label{lemma:stlc-sound}
The |(TTS(stlc))| relation is said to be type preserving if for all elements |envF `stlc` e `rw` e' : tyF| of the transformation relation we have that |(int_(envF)(tyA)) `stlc` e : (int_(tyF)(tyA))| and |(int_(envF)(tyR)) `stlc` e' : (int_(tyF)(tyR))|
\end{lemma}

\begin{proof}
\label{proof:stlc-sound}
This proof follows from straightforward induction. The propagation rules of |(TTS(stlc))| follow identical typing rules as the the underlying STLC object language. The |Tr-Rep| and |Tr-Abs| rules preserve the correctness of typing for both source and result terms. Thus, by induction all terms in the (TTS(stlc)) transformation relation have a typing assignment in the underlying STLC language.
\end{proof}

It is now easy to formulate and show the first TTS property:

\begin{thrm}[Complete |(TTS(stlc))| transformations ensure the first TTS property]
\label{thrm:stlc-type-eq}
For all complete elements |envF `stlc` e `rw` e' : tyF| both terms |e| and |e'| have a valid typing derivation in STLC under the same environment |env| and |ty|.
\end{thrm}

\begin{proof}[Lemma~\ref{lemma:stlc-sound} and completeness imply Theorem~\ref{stlc:stlc-type-eq}]
\label{proof:stlc-type-eq}
From lemma~\ref{lemma:stlc-sound} follows that for some element in the transformation relation |envF `stlc` e `rw` e' : tyF|, we know that |(int_(envF)(tyA)) `stlc` e : (int_(tyF)(tyA))| and |(int_(envF)(tyR)) `stlc` e' : (int_(tyF)(tyR))| are valid typing derivations for |e| and |e'|. From the definition of completeness follows that |(int_(tyF)(tyA)) = (int_(tyF)(tyR))| and
 |(int_(envF)(tyA)) = (int_(envF)(tyR))|. Thus, |e| and |e'| have a valid typing assignment under the same type and type environment in STLC.
\end{proof}
     
\section{|(TTS(stlc))| semantic properties}
The second TTS property dictates that after transformation the semantics of the source and result program are identical. This is formulated by the following Theorem:

\begin{thrm}[Complete |(TTS(stlc))| transformations ensure the second TTS property]
\label{thrm:stlc-term-eq}
For all complete elements |envF `stlc` e `rw` e' : tyF| the equivalence |e `beq` e'| holds.
\end{thrm}

This is a much stronger property than mere type equivalence and is the cause of most of the restrictions that are laid upon the |TTS(stlc)| system. 

\paragraph{Inductive formulation}
The type soundness Lemma~\ref{lemma:stlc-sound} is easy to prove using induction because the TTS follows the structure of the typing rules. To formulate and prove an inductive hypothesis about the semantics of the typed terms is a bit more involved. What is needed is a way to connect the types in the typing rules with the semantics of the terms which are being typed. One way to relate terms and types is with the use of functors.

\subsection{Functors}
A functor can be seen as a function on types. It takes as parameter a type and yields a new type based on its argument. Associated with such a type-level functor is a term-level functor which lifts functions on the type parameter to functions on the functor:

> type F a
> fmap :: (a -> b) -> F a -> F b

For |fmap| to be a proper term-level functor it has to obey the functor laws:

> fmap id = id
> fmap g `comp` fmap f = fmap (g `comp` f)

A list is an example of a Functor in Haskell:

> data List a = Nil | Cons a (List a)

> (fmap_(list)) :: (a -> b) -> List a -> List b
> (fmap_(list)) _ Nil         = Nil
> (fmap_(list)) f (Cons a l)  = Cons (f a) ((fmap_(list)) f l)

What makes functors special, is that an implementation for the term level function |fmap| can be unambiguously constructed from the functor type. In other words: from a given type a term can be derived which adheres to the functor properties. This is the way in which functors connect the term and type world. The rest of this section is dedicated to showing how such a term-level functor can be constructed for the typing functor |tyF|.

This does not work for any type, however. For normal functors, a term-level functor can only be constructed when the argument type occurs in covariant (result) positions within the datatype. This means |fmap| can be constructed for all polynomial types (datatypes without functions), but not for all datatypes containing functions. In the following case a functor can be constructed, because the functor parameter is in a covariant position:

> type IntF a = Int -> a
>
> (fmap_(IntF)) :: (a -> b) -> IntF a -> IntF b
> (fmap_(IntF)) f intf = f `comp` intf

When the type parameter occurs at a covariant (or argument) position, a functor can not be constructed anymore:

> type Func a = a -> a
>
> (fmap_(Func)) :: (a -> b) -> Func a -> Func b
> (fmap_(Func)) f func = f `comp` func `comp` ?

At the question mark a function is needed of the type |b -> a| to convert the argument of type |b| to an argument of type |a|. The function argument is of type |a -> b|, so this does not work. The typing functor |tyF| includes a function space constructor, so to construct a term-level functor for the typing functor, something more powerful than a normal functor is needed.

Meijer and Hutton\cite{meijer} showed that it is possible to define functors for function types (exponential types) with the use of |dimap|s. A |dimap| is the same as the normal |fmap| but with an extra function argument which can be used for occurrences of the type parameter at contra-variant positions.

> (dimap_(F)) :: (b -> a) -> (a -> b) -> F a -> F b

The |Func| example can now be completed with the use of a |dimap|.

> (dimap_(Func)) :: (b -> a) -> (a -> b) -> Func a -> Func b
> (dimap_(Func)) g f func = f `comp` func `comp` g

The functor laws also generalize to the extended functor |dimap|:

> (dimap_(F)) id id = id
> (dimap_(F)) g1 g2 `comp` (dimap_(F)) f1 f2 = (dimap_(F)) (f1 `comp` g1) (g2 `comp` f2)

Note how the first function is contra-variant and the second covariant in the result type when doing composition. 

Based on this work, a term-level |dimap| can be defined for the typing functor |tyF| using the following functor-indexed function:

> (dimap_(tyF)) :: (a -> b) -> (b -> a) -> (tyF_(b)) -> (tyF_(a))
> (dimap_(tyI))                     con cov x = cov x
> (dimap_(T))                       con cov x = x
> (dimap_(tyF_(a) -> (tyF_(r))))  con cov f = (dimap_(tyF_(r))) con cov `comp` f `comp` (dimap_(tyF_(a))) con cov

At the hole position the covariant function is applied to manipulate the hole value. For constant types |T| the |dimap| is just the identity function. Most interesting is the case for function space, which recursively transforms the argument and result of the function, but with the argument functions |con| and |cov| switched for the contra-variant call. Switching these functions 'flips' the type signature of the function from |(tyF_(b)) -> (tyF_(a))| to |(tyF_(a)) -> (tyF_(b))|.

\paragraph{Relating semantics}
To prove Theorem~\ref{thrm:stlc-term-eq} we first prove a more general Lemma which also includes all incomplete terms. Note that for incomplete terms the types may not be equal and thus the semantics between the source and result term may be different. This Lemma makes use of |dimap| to relate the semantics of the result program to the source program and is formalized as follows:

\begin{lemma}[|TTS(`stlc`)| elements have related semantics]
\label{lemma:semantic-relation}
For all elements |envF `stlc` e `rw` e' : tyF| the following equivalence holds:

> (dimap_(tyF)) rep abs ((sub_(envF)) e') `beq` e

\end{lemma}

The difference between the semantics of |e| and |e'| is represented by |(dimap_(tyF)) rep abs|, which is based on the difference in types (embodied in the typing functor). The |abs| and |rep| functions come form the retraction pair that the |TTS(`stlc`)| is instantiated with (see Section~\ref{sec:TTS}). The function |(sub_(envF))| substitutes all free variables in |e'| based on environment |envF|, this is defined by the following function:

> (sub_(envF)) :: (int_(envF)(tyR)) `stlc` e : ty -> (int_(envF)(tyA)) `stlc` e' : ty
> (sub_(empty))          = id
> (sub_(envF, x : tyF))  = (sub_(envF)) `comp` [x `to` (dimap_(tyF)) abs rep x]

This substitution is needed to reason about the semantics of unbound variables and make the equivalence law of Lemma~\ref{lemma:semantic-relation} type correct. This more general Lemma implies the original Theorem~\ref{thrm:stlc-term-eq}. This is easily shown by establishing the following two properties about complete typing functors and complete functor contexts:

\begin{lemma}[|dimap| for a complete functor yields the identity function]
\label{lemma:dimap-complete}
For all complete typing functors |tyF| the equivalence |(dimap_(tyF)) con cov `beq` id| holds for all functions |con| and |cov|.
\end{lemma}

\begin{proof}
\label{proof:dimap-complete}
This follows by induction on the typing functor |tyF|. The hole |Id| is non-existent because |tyF| is complete. The case for base types |T| yields the identity function for |dimap| and thus holds. For function space the induction hypothesis gives the identity for the recursive calls in |dimap| and the composition of two identity functions is $\beta\eta$ equivalent to the identity function itself.
\end{proof}

\begin{lemma}[|(sub_())| for a complete functor context yields the identity function]
\label{lemma:sub-complete}
For all complete functor contexts |envF| the equivalence |(sub_(tyF)) `beq` id| holds.
\end{lemma}  

\begin{proof}
\label{proof:sub-complete}
This follows from induction on |envF|. The empty case is trivial. The extension case is easily shown using equational reasoning:

>   (sub_(envF, x : tyF))
>    `beq` { Expand definition }
>      (sub_(envF)) `comp` [x `to` (dimap_(tyF)) abs rep x]
>    `beq` { Induction hypothesis }
>      id `comp` [x `to` (dimap_(tyF)) abs rep x]
>    `beq` { Lemma|~\ref{lemma:dimap-complete}| }
>      id `comp` [x `to` x]
>    `beq` { Identity substitution }
>      id `comp` id
>    `beq` { Identity composition }
>   id

\end{proof}  


\begin{proof}[Lemma~\ref{lemma:semantic-relation} implies Theorem~\ref{thrm:stlc-term-eq}]
\label{proof:stlc-term-eq}
This proof follows from the assumption of Lemma~\ref{lemma:semantic-relation} and the completeness of the typing functor |tyF| and typing context |envF|.

>   e
>     `beq` { Assumption Lemma{-"~\ref{lemma:semantic-relation}"-} }
>       (dimap_(tyF)) rep abs ((sub_(envF)) e')
>     `beq` { Lemma{-"~\ref{lemma:dimap-complete}"-} }
>       id (sub_(envF) e')
>     `beq` { Def id }
>       (sub_(envF) e')
>     `beq` { Lemma{-"~\ref{lemma:sub-complete}"-} }
>       id e'
>     `beq` { Def id }
>   e'

\end{proof}

Before being able to prove Lemma~\ref{lemma:semantic-relation}, an auxiliary lemma is needed about the behavior of the retraction pair |rep :: tyA -> tyR| and |abs :: tyR -> tyA|. The fact that |tyA| and |tyR| form a retract |tyA `ret` tyR| assures the equivalence |abs (rep x) `beq` x|. For values |x| produced by a |TTS(stlc)| transformation this law should also hold the other way around: |rep (abs x) `beq` x|. A pair of functions which have both these property are called on isomorphism for the isomorphic types |tyA| and |tyR|, denoted by |tyA `iso` tyR|. This yields the following lemma:

\begin{lemma}[A retract behaves as an isomorphism in |TTS(stlc)|]
\label{lemma:ret-iso}
For all elements of the |(TTS(stlc))| relation |envF `stlc` e `rw` e' : Id| the equivalence |rep (abs e') `beq` e'| holds.
\end{lemma}

This lemma is proven by first showing a slightly different statement about what terms |e'| can evaluate to. Normalization for the simply typed lambda calculus is denoted by the function |(eval())|

\begin{lemma}[|tyI| evaluates to |rep|]
\label{lemma:eval-rep}
For all elements of the |(TTS(stlc))| relation |envF `stlc` e `rw` e' : Id| the equivalence |(eval(e')) `beq` rep x| holds for some x.
\end{lemma}
69
116
40
\begin{proof}
\label{lemma:eval-rep}
This follows easily 
\end{proof}
What is left is showing that Lemma~\ref{lemma:semantic-relation} holds for the base |TTS(`stlc`)| relation. This will be proven by induction over the typing rules of |(TTS(stlc))|. 
\begin{proof}
\label{lemma:semantic-equivalence}
Proving by induction over the typing rules means showing that for each typing rule, Lemma~\ref{lemma:semantic-relation} holds for the conclusion of the typing rule assuming that the lemma holds for the premises of the typing rule. Each typing rule will be handled separately:

\paragraph{|Tr-Con|}

\begin{center}
\inferrule{|c is a constant of type ty|}
          {|envF `stlc` c `rw` c : ty|}
\end{center}

The constant rule follows easily because the the |dimap| of a base type (complete type) is the identity function and substitution over a constant equals to the identity substitution.

>   (dimap_(ty)) rep abs ((sub_(envF)) c)
>     `beq` { Lemma{-"~\ref{lemma:dimap-complete}"-} }
>       (sub_(envF)) c
>     `beq` { Substitution over a constant }
>   c

\paragraph{|Tr-Var|} 
\begin{center}
\inferrule{|x : tyF `elem` envF|}
          {|envF `stlc` x `rw` x : tyF|}
\end{center}

The proof for the |Tr-Var| rule follows from the fact that the substitution |(sub_(envF))| and the conversion term |(dimap_(tyF)) rep abs| evaluate to the identity.
                
>   (dimap_(tyF)) rep abs ((sub_(envF)) x)
>    `beq` { x : tyF is an element of envF }
>      (dimap_(tyF)) rep abs ((sub_(envF /x, x : tyF)) x)
>    `beq` { Definition (sub_()) }
>      (dimap_(tyF)) rep abs ((sub_(envF /x)) `comp` [x `to` (dimap_(tyF)) abs rep x] $ x)
>    `beq` { Definition composition }
>      (dimap_(tyF)) rep abs ((sub_(envF /x)) x[x `to` (dimap_(tyF)) abs rep x])
>    `beq` { Apply substitution }
>      (dimap_(tyF)) rep abs ((sub_(envF /x)) ((dimap_(tyF)) abs rep x))
>    `beq` { Definition composition }
>      (dimap_(tyF)) rep abs `comp` (dimap_(tyF)) abs rep $ (sub_(envF /x)) x
>    `beq` { No substitution for x }
>      (dimap_(tyF)) rep abs `comp` (dimap_(tyF)) abs rep $ x
>    `beq` { Functor composition }
>      (dimap_(tyF)) (abs `comp` rep) (abs `comp` rep) x
>    `beq` { Retraction identity }
>     (dimap_(tyF)) id id x
>    `beq` { Functor identity }
>   x

\paragraph{|Tr-Lam|}

\begin{center}
\inferrule{|envF, x : (tyF_(a)) `stlc` e `rw` e' : (tyF_(r))|}   
          {|envF `stlc` \x. e `rw` \x. e' : (tyF_(a)) -> (tyF_(r))|}
\end{center}

The |Tr-Lam| rule is proven by showing that taking a variable |x| from the environment and abstracting over it, also holds for the induction hypothesis. The induction hypothesis gives the following premisse to work with:

> (dimap_(tyF_(r))) rep abs ((sub_(envF , x : (tyF_(a)))) e') `beq` e


>   (dimap_(tyF_(a) -> (tyF_(r)))) rep abs ((sub_(envF)) (\x. e'))
>    `beq` { Commute capture-avoiding substitution over lambda }
>      (dimap_(tyF_(a) -> (tyF_(r)))) rep abs (\x. (sub_(envF /x)) e')
>    `beq` { Definition dimap }
>      (dimap_(tyF_(r))) rep abs `comp` (\x. (sub_(envF /x)) e') `comp` (dimap_(tyF_(a))) abs rep
>    `beq` { Eta expansion }
>      \x. (dimap_(tyF_(r))) rep abs `comp` (\x. (sub_(envF /x)) e') `comp` (dimap_(tyF_(a))) abs rep $ x
>    `beq` { Definition (`comp`) }
>      \x. ((dimap_(tyF_(r))) rep abs ((\x. (sub_(envF /x)) e') ((dimap_(tyF_(a))) abs rep x))
>    `beq` { Evaluation }
>      \x. ((dimap_(tyF_(r))) rep abs ((sub_(envF /x)) e' [x `to` (dimap_(tyF_(a))) abs rep x])
>    `beq` { Definition composition }
>      \x. ((dimap_(tyF_(r))) rep abs ((sub_(envF /x)) `comp` [x `to` (dimap_(tyF_(a))) abs rep x] $ e')
>    `beq` { Definition (sub_()) }
>      \x. (dimap_(tyF_(r))) rep abs ((sub_(envF , x : (tyF_(a)))) e')
>    `beq` { Premise }
>   \x. e

\paragraph{|Tr-App|}
\begin{center}
\inferrule{|envF `stlc` f `rw` f' : (tyF_(a)) -> (tyF_(r))| \\\\
           |envF `stlc` e `rw` e' : (tyF_(a))|}
          {|envF `stlc` f e `rw` f' e' : (tyF_(r))|}
\end{center}

>  (dimap_(tyF_(r))) rep abs ((sub_(envF)) (f' e'))
>   `beq` { Distribute substitution }
>     (dimap_(tyF_(r))) rep abs ((sub_(envF)) f' ((sub_(envF)) e'))
>   `beq` { dimap identity }
>     (dimap_(tyF_(r))) rep abs ((sub_(envF)) f' ((dimap_(tyF_(a))) id id ((sub_(envF)) e')))
>   `beq` { Lemma{-"~\ref{lemma:ret-iso}"-} }
>     (dimap_(tyF_(r))) rep abs ((sub_(envF)) f' ((dimap_(tyF_(a))) (rep `comp` abs) (rep `comp` abs) ((sub_(envF)) e')))
>   `beq` { Functor composition }
>     (dimap_(tyF_(r))) rep abs ((sub_(envF)) f' ((dimap_(tyF_(a))) abs rep `comp` (dimap_(tyF_(a))) rep abs $ (sub_(envF)) e'))
>   `beq` { Definition (`comp`) }
>     (dimap_(tyF_(r))) rep abs `comp` ((sub_(envF)) f') `comp` (dimap_(tyF_(a))) abs rep $ (dimap_(tyF_(a))) rep abs ((sub_(envF)) e'))
>   `beq` { Definition (dimap_(tyF_(a) -> (tyF_(r)))) }
>     (dimap_(tyF_(a) -> (tyF_(r)))) rep abs ((sub_(envF)) f') ((dimap_(tyF_(a))) rep abs ((sub_(envF)) e')))
>   `beq` { Premises }
>  f e

\paragraph{|Tr-Rep|}

\begin{center}
\inferrule{|envF `stlc` e `rw` e' : tyA|}
          {|envF `stlc` e `rw` rep e' : tyI|}
\end{center}

>  (dimap_(tyI)) rep abs ((sub_(envF)) (rep e'))
>   `beq` { Definition (dimap_(tyI)) }
>     abs ((sub_(envF)) (rep e'))
>   `beq` { Commute substitution }
>     abs (rep ((sub_(envF)) e'))
>   `beq` { Retraction }
>     (sub_(envF)) e'
>   `beq` { Definition (dimap_(tyA)) }
>     (dimap_(tyA)) rep abs ((sub_(envF)) e')
>   `beq` { Premise }
>  e
 
\paragraph{|Tr-Abs|}
          
\begin{center}
\inferrule{|envF `stlc` e `rw` e' : tyI|}
          {|envF `stlc` e `rw` abs e' : tyA|}
\end{center}

>  (dimap_(tyA)) rep abs ((sub_(envF)) (abs e'))
>   `beq` { Definition (dimap_(tyA)) }
>     (sub_(envF)) (abs e')
>   `beq` { Commute substitution }
>     abs ((sub_(envF)) e')
>   `beq` { Definition (dimap(tyI)) }
>     dimap_Id rep abs ((sub_(envF)) e')
>   `beq` { Premise }
>  e
\end{proof}
