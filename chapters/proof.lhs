The goal of a TTS transformation relation is to enforce the transformation properties as defined at the beginning of section~\ref{subsec:properties}. This chapter is dedicated to showing that this is indeed the case for the base system of |(TTS(stlc))|. The main theorem shown here is formulated as follows:

\begin{thrm}[Complete |(TTS(stlc))| Transformations Ensure the transformation properties]
\label{thrm:stlc-tts}
For all complete elements |(lift(env)) `stlc` e `rw` e' : T| from the relation |(TTS(stlc))|, the transformation |e `rw` e'| adheres to the transformation properties.
\end{thrm}

The first three section of this chapter show the Productivity, Soundness and Equivalence property for |(TTS(stlc))|. The last two sections reflect on the theoretical background of the type and transform system.

\section{\texorpdfstring{|(TTS(stlc))|}{TTS stlc} preserves Typing}
\label{sec:typing}
A complete transformation is defined to be a transformation which is typed with a base type and for which the environment is complete (contains no holes). This means that, as long as the simultaneous typing system is sound with respect to the typing system of stlc, a complete transformation will result in two equally typed terms. This type soundness property is formalized by the following lemma:

\begin{lemma}[Soundness of |(TTS(stlc))|]
\label{lemma:stlc-sound}
The |(TTS(stlc))| relation is sound if for all elements |envF `stlc` e `rw` e' : tyF| of the transformation relation we have that |(int_(envF)(tyA)) `stlc` e : (int_(tyF)(tyA))| and |(int_(envF)(tyR)) `stlc` e' : (int_(tyF)(tyR))| have a valid typing derivation.
\end{lemma}

\begin{proof}
\label{proof:stlc-sound}
The evidence for this property follows from straightforward induction. The propagation rules of |(TTS(stlc))| follow identical typing rules as the the underlying STLC object language, and thus preserve the typing of the transformed terms. The |Tr-Rep| and |Tr-Abs| rules preserve the correctness of typing for both source and result terms. Thus, by induction all terms in the |(TTS(stlc))| transformation relation have a typing assignment in the underlying STLC language.
\end{proof}

\noindent It is now easy to state more formally that TTS property~\ref{prop:types} holds in |(TTS(stlc))|:

\begin{thrm}[Complete Transformations ensure TTS property~\ref{prop:types}]
\label{thrm:stlc-type-eq}
For all complete elements |(lift(env)) `stlc` e `rw` e' : T| both terms |e| and |e'| have equal type assignments |env `stlc` e : T| and |env `stlc` e' : T| in the simply typed lambda calculus.
\end{thrm}

\begin{proof}[\ref{lemma:stlc-sound} and Completeness imply~\ref{thrm:stlc-type-eq}]
\label{proof:stlc-type-eq}
From lemma~\ref{lemma:stlc-sound} follows that for a complete element in the transformation relation |(lift(env)) `stlc` e `rw` e' : T|, we know that here exist valid typing derivations for |(int_(env(lift))(tyA)) `stlc` e : T| and |(int_(lift(env))(tyR)) `stlc` e' : T|. From the definition of a complete environment simply follows that |(int_(lift(env))(ty))| for all |ty|. Thus, |env `stlc` e : T| and |env `stlc` e' : T| are valid typing assignments in STLC with the same type and type environment.
\end{proof}

\section{\texorpdfstring{|(TTS(stlc))|}{TTS stlc} is Productive}
\label{sec:productivity}
To show that a program transformation always produces a result, it is enough to show that the transformation system admits the identity transformation: A program can always be transformed into itself. More formally, the following theorem has to be shown:

\begin{thrm}[|(TTS(stlc))| admits the identity transformation]
\label{thrm:identity}
For all well-typed terms |env `stlc` e : ty| an identity transformation exists with the judgement |(lift(envF)) `stlc` e `rw` e : ty|.
\end{thrm}

\begin{proof}[|(TTS(stlc))| admits the identity transformation]
\label{proof:identity}
The existence of the propagation rules makes that the identity transformation can always be constructed. Each rule in the stlc typing derivation has a matching rule in |(TTS(stlc))| which can always be applied.
\end{proof}

\section{\texorpdfstring{|(TTS(stlc))|}{TTS stlc} preserves Semantics}
\label{sec:semantics}
The third TTS property states that two terms should be semantically equivalent. Semantic equivalence is proven by showing $\beta\eta$-convertibility of the source and result term under all closing environments, as formulated in as the following property:

\begin{lemma}[Complete |(TTS(stlc))| transformations preserve semantics]
\label{lemma:stlc-sem-eq}
For all complete elements |(lift(env)) `stlc` e `rw` e' : T| of the typing relation, |(close(e)(sub)) `beq` (close(e')(sub))| for all closing substitutions |sub|.
\end{lemma}

|(subst(e)(s))| represents capture-avoiding substitution of s in e. A closing substitution is a substitution which substitutes all free variables for closed terms. This is represented by the following construction:

> (closure(empty))    = id
> (closure(sub , x))  = [x `to` e] `comp` (closure(sub))

Lemma~\ref{lemma:stlc-sem-eq} is proven with the use of a logical relations.

\subsection{Logical Relations}
A proof by logical relations is a proof methodology which has been very useful for proving properties about programming languages based on the simply typed lambda calculus. The fundamentals of logical relations are explained here, for further reading the reader is referred to Mitchell~\cite{mitchell96}, Hinze~\cite{hinze00} or Schurmann\cite{schurmann08}.

A logical relation represents a property over a term, or between multiple terms. Characteristic of a logical relation is that the represented property depends on the type of the term(s) over which the property is established. For base types this is often a simple judgement formulated in some logic. At function types the relation establishes that inputs related by the logical relation result in outputs related by the logical relation. Thus a typical unary logical relation for the simply typed lambda calculus looks as follows:

> (rel1(e)(T))                   = (judge(e))
> (rel1(e)(ty_(a) -> (ty_(r))))  = forall a : (rel1(a)(ty_(a))) `imp` (rel1(e a)(ty_(r)))

Here |(judge(e))| represents some property of the term |e|. The case for function terms states that function application should preserve this property. The logical relation may be stated in any logic, but is often represented in set-theory. Another way to look at logical relations is as an induction hypothesis indexed by types.

\subsection{A Logical Relation for \texorpdfstring{|(TTS(stlc))|}{TTS stlc}}
|(TTS(stlc))| constructs a transformation between two terms |e| and |e'|, typed by a typing functor |tyF|. Thus the logical relation becomes a binary logical relation over |e| and |e'|, indexed by the typing functor |tyF|. To deal with free variables the relation is parametrized by closing substitutions to close the terms. This leads to the following logical relation for |(TTS(stlc))|.

> (relV(tyI))                   sub sub' e e' = rep ((subst(e)(cls))) `beq` (subst(e')(cls'))
> (relV(T))                     sub sub' e e' = (subst(e)(cls)) `beq` (subst(e')(cls'))
> (relV(tyF_(a) -> (tyF_(r))))  sub sub' e e' = forall a a' : (relV(tyF_(a))) sub sub' a a' `imp` (relV(tyF_(r))) sub sub' (e a) (e' a')

The basic property that is being established is $\beta\eta$-convertibility between the source and result term. The case for the hole type |tyI| represents that the source term can be transformed into the result term by applying the function |rep|. For base types we expect both terms to be convertible. The function type establishes that related transformations result in related transformations when applied.

The logical relation extends naturally from single terms to closing substitutions. Two closing substitutions are related when they substitute related terms for equal variables. Note that equal variables may have different types in the source and result terms, but are indexed by the same variable in the functor context. The relation for closing substitutions is indexed by the types in the functor context, which it closes.

> (relE(empty))       id                       id                         = empty
> (relE(envF , tyF))  ([x `to` i] `comp` sub)  ([x `to` i'] `comp` sub')  = (relE(envF)) sub sub' , (relV(tyF)) sub sub' i i'

\subsection{Proof using logical relations}
When constructing a proof using logical relations, the proof is usually constructed using two key theorems, occurring in roughly the following form:

\begin{enumerate}
  \item Fundamental theorem: the relation |(rel1(e)(ty))| can be established for all terms |e : ty|
  \item Extraction theorem: terms related by |(rel1(e)(ty))| give rise to some property |(prop(e))|
\end{enumerate}

It is easy to see that the combination of these two theorems can be used to prove the property |(prop(e))| for all |e : ty|. This same approach is taken here, leading to the following key theorems to show that a transformation in |(TTS(stlc))| is semantics preserving.

\begin{thrm}[Fundamental Theorem for |(TTS(stlc))|]
\label{thrm:fundamental-theorem}
For all term |e| and |e'| for which a transformation deduction |envF `stlc` e `rw` e' : tyF| exists, the logical relation |(relV(tyF)) sub sub' e e'| holds under all related environments |(relE(envF)) sub sub'|.
\end{thrm}

\begin{thrm}[Extraction Theorem for |(TTS(stlc))|]
\label{thrm:extraction-theorem}
For all complete terms |env `stlc` e : T|, |env `stlc` e' : T| and term closure |sub : (closure(env))|, the relation |(relV(T)) sub sub e e'| implies |(close(e)(sub)) `beq` (close(e')(sub))|.
\end{thrm}

\begin{corollary}[A Substitution Environment is related to Itself]
\label{corollary:rel-env}
An important corollary of the Fundamental Theorem and Identity Transformation property, is that a substitution environment is related to itself. This follows from the fact that all terms in the environment have an identity transformation and according to the fundamental theorem each valid transformation is part of the logical relation.
\end{corollary}

\begin{proof}[Extraction Theorem]
\label{proof:extraction-theorem}
The proof for the extraction theorem is immediate, because the logical relation |(relV(T)) sub sub e e'| on base types is defined as |(close(e)(sub)) `beq` (close(e')(sub))|.
\end{proof}

With these properties established it is now possible to show that |(TTS(stlc))| is semantics preserving.

\begin{proof}[The Fundamental Theorem and Extraction Theorem imply~\ref{lemma:stlc-sem-eq} ]
\label{proof:stlc-sem-eq}
The Fundamental Theorem shows that all complete elements are |(lift(env)) `stlc` e `rw` e' : T| logically related , with aid of Corollary~\ref{corollary:rel-env} which shows that substitution environments are always related to themselves.
The Extraction Theorem shows that logical relations give rise to $\beta\eta$-equality for complete terms, thus
|(close(e)(sub)) `beq` (close(e')(sub))| for all |sub|.
\end{proof}

What is left is showing the fundamental theorem for |(TTS(stlc))|.

\paragraph{Fundamental theorem}
Before showing the fundamental theorem, two properties among logical relations have to be established. These properties are stated as 'logical equivalences' between two logical relations, meaning that either both relations hold, or they both do not hold. They always have the same truth value.

The first lemma establishes that |(relV(tyF))| is closed under $\beta\eta$-equivalence of the related terms. The second lemma is the Crossing Lemma, which shows that substitutions can be commuted between the closing environments and the related terms. This lemma is the key to showing the logical relation under beta reduction.

\begin{lemma}[|(relV(tyF))| is Closed under $\beta\eta$-equality]
\label{lemma:rel-beta-eta}
Two logical relations |(relV(tyF)) sub sub' e e'| and |(relV(tyF)) sub sub' f f'| are logically equivalent when |e `beq` f| and |e' `beq` f'|.
\end{lemma}

\begin{lemma}
\label{lemma:crossing}
For any two terms |i| and |i'| in which |x| does not appear free, the relation |(relV(tyF)) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') e e'| is logically equivalent to |(relV(tyF)) sub sub' (e @ [x `to` i]) (e' @ [x `to` i'])|.
\end{lemma}

Both lemmas are proven at the end of this paragraph on page~\pageref{proof:rel-beta-eta}, first the fundamental theorem is shown.

\begin{proof}[Proof of the Fundamental Theorem]
\label{proof:fundamental-theorem}
The fundamental theorem shows that all terms |e| and |e'| arising from a transformation derivation |envF `stlc` e `rw` e' : tyF| give rise to an element in the logical relation |(relV(tyF)) sub sub' e e'|, under all related environments |(relE(envF)) sub sub'|. This is shown by induction on the deduction rules of |(TTS(stlc))|.

\begin{itemize}
  \item[|Tr-Con|] \boxed{\inferrule{|c is a constant of type T|}
                         {|envF `stlc` c `rw` c : T|}}

Here we have to show the logical relation for base types: |(close(c)(sub)) `beq` (close(c)(sub'))|, which is trivially true for constants.

>   (close(c)(sub))
>`beq` { Substitution over constants }
>   c
>`beq` { Substitution over constants }
>   (close(c)(sub'))

  \item[|Tr-Var|] \boxed{\inferrule{|x : tyF `elem` envF|}
                         {|envF `stlc` x `rw` x : tyF|}}

Relatedness of variables is shown 'under related substitution environments', which contain two related terms |i| and |i'| for each free variable:

>  (relE(envF , x)) (x @ [x `to` i]) (x @ [x `to` i'])
>`imp` { Extract related terms for variable x }
>  (relV(tyF)) sub sub' i i'
>`imp` { Substitution }
>  (relV(tyF)) sub sub' (x @ [x `to` i]) (x @ [x `to` i'])
>`imp` { Crossing lemma }
>  (relV(tyF)) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') x x

  \item[|Tr-Lam|] \boxed{\inferrule{|envF, x : (tyF_(a)) `stlc` e `rw` e' : (tyF_(r))|}
                                   {|envF `stlc` \x. e `rw` \x. e' : (tyF_(a)) -> (tyF_(r))|}}

The lambda rule shows that related inputs result in related outputs under beta-reduction. The following statement is to be shown: |(relV(tyF_(a))) sub sub' a a' `imp` (relV(tyF_(r))) sub sub' ((\x. e) a) ((\x. e') a')| 

>   (relV(tyF_(a))) sub sub' a a'
>`imp` { Induction hypothesis on e and e' with related a and a' in the environment }
>   (relV(tyF_(r))) ([x `to` a] `comp` sub) ([x `to` a'] `comp` sub') e e'
>`imp` { Crossing lemma }
>   (relV(tyF_(r))) sub sub' (e @ [x `to` a]) (e' @ [x `to` a'])
>`imp` { Relation is closed under beta-eta equivalence }
>   (relV(tyF_(r))) sub sub' ((\x. e) a) ((\x. e') a')

  \item[|Tr-App|] \boxed{\inferrule{|envF `stlc` f `rw` f' : (tyF_(a)) -> (tyF_(r))| \\\\
                                    |envF `stlc` e `rw` e' : (tyF_(a))|}
                                   {|envF `stlc` f e `rw` f' e' : (tyF_(r))|}}

The logical relation already establishes that related inputs result in related outputs for related terms. This makes the application rule trivial to prove. The following needs to be shown: |(relV(ty_(r))) sub sub' (f e) (f' e')| 

>`imp` { Induction on e and e' }
>  (relV(ty_(a))) sub sub' e e'
>`imp` { Induction on f and f' and modus ponens }
>  (relV(ty_(r))) sub sub' (f e) (f' e')

  \item[|Tr-Rep|] \boxed{\inferrule{|envF `stlc` e `rw` e' : tyA|}
                                   {|envF `stlc` e `rw` rep e' : tyI|}}

The logical relation for the hole type |Id| dictates that |rep| applied to the source term should be $\beta\eta$-equivalent to the result term. Thus for the rep rule we simple need to show that |rep (close(e)(sub)) `beq` (close(rep e')(sub'))|.

>   rep (close(e)(sub))
>`beq` { Induction hypothesis }
>   rep (close(e')(sub'))

  \item[|Tr-Abs|] \boxed{\inferrule{|envF `stlc` e `rw` e' : tyI|}
                                   {|envF `stlc` e `rw` abs e' : tyA|}}

To prove the |Tr-Abs| rule, the fact that |abs| and |rep| are a retraction pair is needed. The statement to prove is |(close(e)(sub)) `beq` (close(abs e')(sub'))|.

>  (close(e)(sub))
>`beq` { Retraction pair abs and rep }
>  abs (rep (close(e)(sub)))
>`beq` { Induction hypothesis }
>  abs (close(e')(sub'))

\end{itemize}
\end{proof}

What is left is showing the \ref{lemma:rel-beta-eta} and \ref{lemma:crossing} used in this proof.

\begin{proof}[Proof of \ref{lemma:crossing}]
\label{proof:crossing}
Logical equivalence is proven by showing implication in both directions. In both directions the proof is carried out by induction on the typing functor |tyF|. The two implications directions are proven by mutual induction: both directions of the bi-implication make use of the other direction to prove themselves. While this may seem like cyclic reasoning, it is not, because the induction hypothesis is only ever called on smaller types.


\paragraph{Proof in the direction:} |(relV(tyF)) sub sub' (e @ [x `to` i]) (e' @ [x `to` i'])| implies |(relV(tyF)) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') e e'|.
\begin{itemize}
  \item[|Id|] case, showing |rep (close(e @ [x `to` i])(sub)) `beq` (close(e' @ [x `to` i'])(sub'))|
>  rep (close(e)([x `to` i] `comp` sub))
>`beq` { Definition substitution and close }
>  rep (close((e @ [x `to` i]))(sub))
>`beq` { Premise }
>  (close((e' @ [x `to` i']))(sub'))
>`beq` { Definition substitution and close }
>  (close(e')([x `to` i'] `comp` sub'))
  \item[|T|] case is analogous to the |Id| case.
  \item[|(ty_(a)) -> (ty_(r))|] case, showing |(relV(tyF_(a))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') a a' `imp` (relV(tyF_(r))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') (e a) (e' a')|
>   (relV(tyF_(a))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') a a'
>`imp` { Crossing lemma }
>   (relV(tyF_(a))) sub sub' (a @ [x `to` i]) (a' @ [x `to` i'])
>`imp` { Premise }
>   (relV(tyF_(r))) sub sub' (e a @ [x `to` i]) (e a' @ [x `to` i'])
>`imp` { Induction }
>   (relV(tyF_(r))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') (e a) (e' a')
\end{itemize}

\paragraph{Proof in the direction:} |(relV(tyF)) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') e e'| implies |(relV(tyF)) sub sub' (e @ [x `to` i]) (e' @ [x `to` i'])|.
\begin{itemize}
  \item[|Id|] case, showing |rep (close(e)([x `to` i] `comp` sub)) `beq` (close(e')([x `to` i'] `comp` sub'))|
>  rep (close((e @ [x `to` i]))(sub))
>`beq` { Definition substitution and close }
>  rep (close(e)([x `to` i] `comp` sub))
>`beq` { Premise }
>  (close(e')([x `to` i'] `comp` sub'))
>`beq` { Definition substitution and close }
>  (close((e' @ [x `to` i'])m)(sub'))
  \item[|T|] case is analogous to the |Id| case.
  \item[|(ty_(a)) -> (ty_(r))|] case, showing |(relV(tyF_(a))) sub sub' a a' `imp` (relV(tyF_(r))) sub sub' ((e @ [x `to` i]) a) ((e' @ [x `to` i']) a')|
>   (relV(tyF_(a))) sub sub' a a'
>`imp` { Substitution on unbound variable x in a }
>   (relV(tyF_(a))) sub sub' (a @ [x `to` i]) (a' @ [x `to` i'])
>`imp` { Crossing lemma }
>   (relV(tyF_(a))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') a a'
>`imp` { Premise }
>   (relV(tyF_(r))) ([x `to` i] `comp` sub) ([x `to` i'] `comp` sub') (e a) (e a')
>`imp` { Induction }
>   (relV(tyF_(r))) sub sub' (e a @ [x `to` i]) (e a' @ [x `to` i'])
>`imp` { x is unbound in a }
>   (relV(tyF_(r))) sub sub' ((e @ [x `to` i]) a) ((e' @ [x `to` i']) a')
\end{itemize}

\end{proof}

\begin{proof}[Proof of \ref{lemma:rel-beta-eta}]
\label{proof:rel-beta-eta}
The proof is by induction on |tyF|. Due to the symmetric nature of this statement it is only necessary to prove this property in one direction, although 
\begin{itemize}
  \item[|Id|] case, proving: |rep (close(f)(sub)) `beq` (close(f')(sub'))|
>  rep (close(f)(sub))
>`beq` { Premise e `beq` f and symmetry }
>  rep (close(e)(sub))
>`beq` { Premise }
>  (close(e')(sub'))
>`beq` { Premise }
>  (close(f')(sub'))
  \item[|T|] case is analogous to the |Id| case.
  \item[|(ty_(a)) -> (ty_(r))|] case, showing for all |a| and |a'|: |(relV(ty_(a))) sub sub' a a' `imp` (relV(ty_(r))) sub sub' (f a) (f' a')| given the premises.
>  (relV(ty_(a))) sub sub' a a'
>`beq` { Premise }
>  (relV(ty_(r))) sub sub' (e a) (e a')
>`beq` { Induction hypothesis with extended premises: e a `beq` f a and e' a' `beq` f' a' }
>  (relV(ty_(r))) sub sub' (f a) (f a')
\end{itemize}
\end{proof}

\section{Hughes' Strings Transformation Preserves the TTS Properties}
We can now show that the Hughes' Strings instantiation of |(TTS(stlc))| is a valid TTS transformation by extending the base proof for |(TTS(stlc))|. Two additional propeties have to be established:
\begin{itemize}
  \item It needs to be shown that |(abs_(ss))| and |(rep_(ss))| form a retraction pair, because this is a premise of |(TTS(stlc))|. A retraction pair has the property that |(abs_(ss)) `comp` (rep_(ss)) == id|.
  \item An extra case has to be added to the Fundamental Theorem for the |Tr-Comp| rewrite rule.
\end{itemize}

A retraction is proven through straightforward equational reasoning.

\begin{proof}[|(abs_(ss))| and |(rep_(ss))| form a retraction]
>   (abs_(ss)) `comp` (rep_(ss))
>`beq` { Eta expansion }
>   \x -> ((abs_(ss)) `comp` (rep_(ss))) x
>`beq` { Definition composition }
>   \x -> (abs_(ss)) ((rep_(ss)) x)
>`beq` { Defintition of (rep_(ss)) }
>   \x -> (abs_(ss)) (x ++)
>`beq` { Definition of (abs_(ss)) }
>   \x -> x ++ ""
>`beq` { Definition of (++) }
>   \x -> x
>`beq` { Definition of identity }
>   id
\end{proof}

The extra case for |Tr-Comp| for the Fundamental Theorem shows that the |Tr-Comp| rule adheres to the logical relation. Because the |Tr-Comp| rule contains only base types, this boils down to the following lemma:

\begin{lemma}[|Tr-Comp| support the Fundamental Theorem]
\label{lemma:tr-comp}
For all environments |s| and |s'| and related terms |(rep_(ss)) (close(a)(s)) `beq` (close(a')(s'))| and |(rep(ss)) (close(b)(s)) `beq` (close(b')(s'))| we have that |(close((rep_(ss)) (a ++ b))(s)) `beq` (close(a' `comp` b')(s'))|.
\end{lemma}

\begin{proof}[|Tr-Comp| support the Fundamental Theorem]
>   (close((rep_(ss)) (a ++ b))(s)) 
>`beq` { Definition (rep_(ss)) }
>   (close(((a ++ b) ++))(s)) 
>`beq` { Commute substitution }
>   ((close(a)(s)) ++ (close(b)(s))) ++
>`beq` { Eta expansion }
>   \x. ((close(a)(s)) ++ (close(b)(s))) ++ x
>`beq` { Associativity (++) }
>   \x. (close(a)(s)) ++ ((close(b)(s)) ++ x)
>`beq` { Definition (`comp`) }
>   \x. ((close(a)(s)) ++) `comp` ((close(b)(s)) ++) x
>`beq` { Eta reduction }
>   ((close(a)(s)) ++) `comp` ((close(b)(s)) ++)
>`beq` { Definition (rep_(ss)) }
>   (rep_(ss)) (close(a)(s)) `comp` (rep_(ss)) (close(b)(s))
>`beq` { Premises }
>   (close(a')(s')) `comp` (close(b')(s'))
>`beq` { Definition substitution }
>   (close(a' `comp` b')(s'))
\end{proof}

\section{Type Abstraction}
\label{sec:type-abstraction}
Taking back a step, we can see that the ideas of the type and transform system are firmly rooted in the idea of type abstraction, or representation independence as it is called in Mitchell~\cite{mitchell96}. The idea of type abstraction is the idea that the implementation of a datatype can be freely changed, as long as this results in the same external behavior. This makes it possible for the creators of compilers to change for example the representation of integers without breaking all software, as long as all functions on integers yield comparable results.

In our transformation system, the |abs| and |rep| functions make it possible to locally change the representation of a type, making it possible to switch to a different type  in limited parts of the program. The requirement of the type and transform system that the transformed types form a retraction and that each transformed term is related to another transformed term can be seen as showing that the transformed type is just a different implementation for the original type. In the case of Hughes' strings the relatedness of |Tr-Comp| and the left inverse of |(rep_(ss))| and |(abs_(ss))| show that |String -> String| can be a replacement implementation for |String| under the idea of type abstraction. 

\begin{comment}
The idea of an abstract and a representation type was already present in Hughes' work~\ref{hughes86}. Type and transform systems can be seen as a generalization of 
\end{comment}
\section{The Typing Functor is an actual Functor}
\label{sec:functor}

%include functor.lhs
