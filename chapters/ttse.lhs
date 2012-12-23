Although the simply typed lambda calculus is a convenient language with which to explain ideas and prove general concepts, it is too simple to serve as a basis for real-world transformation systems. Most notably, STLC does not support recursion or polymorphism, two constructs which are present in almost all real-world functional languages.

This chapter introduces such fundamental extensions for the basic |(TTS(stlc))| along several axis. The soundness  of these extensions is not proven here but is informally shown and provability is briefly discussed.

\section{Extending to let-polymorphism}
One of the most common extensions to the simply typed lambda calculus is let-polymorphism with Hindley-Milner typing as found in ML and Haskell. This extension introduces the concept of type variables into the language and a way to quantify over them, as in the following definitions:

> ty    ::= T | a | ty -> ty
> sch   ::= forall a. sch | ty
> env   ::= env , sch | empty
> sbst  ::= [a `to` ty] `comp` sbst | id

The typing functor of |(TTS(stlc))| is essentially an extension of the base types, and thus works equally well in the presence of type variables:

> tyF    ::= T | Id | a | tyF -> tyF
> schF   ::= forall a. schF | tyF
> envF   ::= envF , schF | empty
> sbstF  ::= [a `to` tyF] `comp` sbstF | id

Hindley-Milner typing prescribes two functions which can be used to introduce and eliminate quantification, |gen :: env -> ty -> sch| and |inst :: sch -> sbst -> ty|. Generalize quantifies over all type variables in |ty| except the variables which occur free in the environment |env|. |inst| creates a normal type from a schema and a substitution |sbst| for all quantified variables. These function can be straightforwardly extended to typing functors by treating the |Id| construct as a normal base type in both functions.

Figure~\ref{fig:letrules} shows the typing rules for the let-polymorphic lambda calculus and the corresponding transformation rules for |(TTS(let))|, the core transformation system. The extension is again a straightforward extension of the basic Hindley-Milner typing rules. Proving this transformation correct however is more difficult.

\begin{figure}[t]
\begin{tabular}{l r c l r}
|Tr-Con|
&\inferrule{|c is a constant of type T|}
           {|envF `lt` c `rw` c : T|}
&\quad
&\inferrule{|c is a constant of type T|}
           {|env `lt` c : T|}
&|Con|
\\
|Tr-Var|
&\inferrule{|x : schF `elem` envF|}
           {|envF `lt` x `rw` x : instF(schF, sub)|}
&\quad
&\inferrule{|x : sch `elem` env|}
           {|env `lt` x : inst(sch, sbst)|}
&|Var|
\\
|Tr-Lam|
&\inferrule{|envF, x : (tyF_(a)) `lt` e `rw` e' : (tyF_(r))|}
           {|envF `lt` \x. e `rw` \x. e' : (tyF_(a)) -> (tyF_(r))|}
&\quad
&\inferrule{|env, x : (ty_(a)) `lt` e : (ty_(r))|}
           {|env `lt` \x. e : (ty_(a)) -> (ty_(r))|}
&|Lam|
\\
|Tr-App|
&\inferrule{|envF `lt` f `rw` f' : (tyF_(a)) -> (tyF_(r))| \\\\
            |envF `lt` e `rw` e' : (tyF_(a))|}
           {|envF `lt` f e `rw` f' e' : (tyF_(r))|}
&\quad
&\inferrule{|env `lt` f : (ty_(a)) -> (ty_(r))| \\\\
            |env `lt` e : (ty_(a))|}
           {|env `lt` f e : (ty_(r))|}
&|App|
\\
|Tr-Let|
&\inferrule{|envF `lt` f `rw` f' : (tyF_(a))| \\\\
            |envF , x : genF(envF, (tyF_(a))) `lt` e `rw` e' : (tyF_(r))|}
           {|envF `lt` let x = f in e `rw` let x = f' in e' : (tyF_(r))|}
&\quad
&\inferrule{|env `lt` f : (ty_(a))| \\\\
            |env , x : gen(env, (ty_(a))) `lt` e : (ty_(r))|}
           {|env `lt` let x = f in e : (ty_(r))|}
&|Let|
\\
|Tr-Rep|
&\inferrule{|envF `lt` e `rw` e' : tyA|}
           {|envF `lt` e `rw` rep e' : tyI|}
\\
|Tr-Abs|
&\inferrule{|envF `lt` e `rw` e' : tyI|}
           {|envF `lt` e `rw` abs e' : tyA|}
\\
|Judgement|
&\boxed{|envF `lt` e `rw` e' : tyF|}
&\quad
&\boxed{|env `lt` e : ty|}
\end{tabular}
\caption{Type checking rules for the propagation relation of |(TTS(let))|}
\label{fig:letrules}
\end{figure}

\begin{comment}
\paragraph{Proof} Because the typing language of |(TTS(let))| is extended with variables and quantification, the logical relation needs to deal with those typing constructs as well. 
\end{comment}

\section{Including a fixpoint}
Although the simply typed lambda calculus serves well as a foundation for a typed program transformation system, it has one important shortcoming: it is not Turing complete. A language needs some form of unbridled recursion to become Turing complete. A well-known construct for recursion is the fixpoint. A fixpoint works by taking a function and turning it into a possibly infinite self-application. An example of a fixpoint is the Y combinator, but other variants exist as well.

> fix :: (a -> a) -> a
> fix f = (\x -> f (x x)) (\x -> f (x x))

Note that this expression does not type-check in Haskell. There are ways to make such a primitive recursion operator type-check but usually the fixpoint is an internal part of a language. Programs containing general recursive functions are compiled into a version containing only fixpoints as recursion primitive. A typing rule and propagation rule for a primitive |fix| can be constructed as follows:

\begin{figure}[h]
\begin{tabular}{l r c l r}
|Tr-Fix|
&\inferrule{|envF `stlc` f `rw` f' : T -> T|}
           {|envF `stlc` fix f `rw` fix f' : T|}
&\quad
&\inferrule{|env `stlc` f : T -> T|}
           {|env `stlc` fix f : T|}
&|Fix|
\\
\end{tabular}
\end{figure}

Because |fix| is a primitive function, it has a separate convertibility rule, $\mu$, which states that one of the function applications can be peeled off the infinite chain of self-applications.

>   mu     : ∀ {τ} → {f : Γ ⊢ τ ⇒ τ} → fix f βη-≡ f · fix f
>   %fix   : ∀ {τ} → {f f' : Γ ⊢ τ ⇒ τ} → f βη-≡ f' -> fix f βη-≡ fix f'

While this seems like a straightforward enough extension to the basic |(TTS(stlc))| system, the fixpoint has some implications on the semantics of a language, and thus on the way proofs are conducted for that language. 

\paragraph{Impact on evaluation}
The main problem is that a fixpoint introduces possibly infinite recursion: divergent terms. This means that, next to the normal values which a term can produce, a term can also produce $\bot$: no value at all! In such a language, the order of evaluation becomes important.

The lambda calculus without fixpoint is \emph{strongly normalizing}, meaning that however evaluation is performed, the answer will always be the same. However, with the presence of $\bot$, the order of evaluation can have an impact on the result of evaluation. This is best illustrated with an example:

> v = take 10 (fix (1:))

|fix (1:)| produces an infinite list of 1's. The outcome of this function now really depends on what is evaluated first. If the arguments to a function are evaluated before a function is called, this program will loop forever. If, however, functions are being reduced before their arguments, this program will produce a list of 10 1's. The first type of evaluation is called call-by-value or strict evaluation, the second is called call-by-need or lazy evaluation.

This example shows that lazy evaluation can sometimes produce an answer when strict evaluation can not. This is because lazy evaluation has a very nice property which strict evaluation lacks: if a term can produce a value (has a \emph{normal form}), lazy evaluation will compute this value.

\paragraph{Convertibility}
The fact that the evaluation order impacts the final outcome of an expression also impacts equational reasoning and the convertibility relation. Take for example the following equality:

> const 1 (fix (:1)) `beq` 1

In a lazy semantics this would be a valid equality. In a strict semantics this is unequal: |fix (:1)| has to be evaluated be evaluated before |const| and will thus result in $\bot$ instead of |1|. In general, the convertibility relation is only sound for semantics which use \emph{lazy evaluation}. This also means that the proofs in the type and transform system are only valid for a language with lazy semantics.

\paragraph{Totality} Convertibility can be made sound in a strict language by restricting the |fix| function to functions which provably never produce $\bot$: they never loop. A provably finite recursive function is called a \emph{total} function. Agda is an example of a language which allows equational reasoning because, although it has strict semantics, it requires totality on its functions. Note that limitation again removes the turing completeness from a language.

