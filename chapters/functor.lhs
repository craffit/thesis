The typing functor is the heart of the type and transform system. The use of this functor gives rise to both the type-correctness as well as the semantic correctness of |(TTS(stlc))| through the logical relation. The fact that this works out is because the typing functor is defined as an actual functor as known in the field category theory. It is purely out of theoretical curiosity that we show this here. Before showing that the typing functor is a proper functor, we introduce the concept of functors and difunctors.

\paragraph{Functors}
A functor can be seen as a function on types. It takes as parameter a type and yields a new type based on its argument. Associated with such a type-level functor is a term-level functor which lifts functions on the type parameter to functions on the functor:

> type F a
> fmap :: (a -> b) -> F a -> F b

For |fmap| to be a proper term-level functor it has to obey the functor laws:

> fmap id = id
> fmap g `comp` fmap f = fmap (g `comp` f)

A list is an example of a functor in Haskell:

> data List a = Nil | Cons a (List a)

> (fmap_(list)) :: (a -> b) -> List a -> List b
> (fmap_(list)) _ Nil         = Nil
> (fmap_(list)) f (Cons a l)  = Cons (f a) ((fmap_(list)) f l)

What makes functors special, is that an implementation for the term level function |fmap| can be unambiguously constructed from the functor type. In other words: from a given type a term can be derived which adheres to the functor properties. This is the way in which functors connect the term and type world. The rest of this section is dedicated to showing how such a term-level functor can be constructed for the typing functor |tyF|.

For normal functors, a term-level functor can only be constructed when the argument type occurs in covariant (result) positions within the datatype. This means |fmap| can be constructed for all polynomial types (datatypes without functions), but not for all datatypes containing functions. In the following case a functor can be constructed, because the functor parameter is in a covariant position:

> type IntF a = Int -> a
>
> (fmap_(IntF)) :: (a -> b) -> IntF a -> IntF b
> (fmap_(IntF)) f intf = f `comp` intf

When the type parameter occurs at a contravariant (or argument) position, a functor can not be constructed anymore:

> type Func a = a -> a
>
> (fmap_(Func)) :: (a -> b) -> Func a -> Func b
> (fmap_(Func)) f func = f `comp` func `comp` ?

At the question mark a function is needed of the type |b -> a| to convert the argument of type |b| to an argument of type |a|. The function argument is of type |a -> b|, so this does not work. The typing functor |tyF| includes a function space constructor, so to construct a term-level functor for the typing functor something more powerful than a normal functor is needed.

Meijer and Hutton\cite{meijer95} showed that it is possible to define functors for function types (exponential types) with the use of |dimap|s. A |dimap| is the same as the normal |fmap| but with an extra function argument which can be used for occurrences of the type parameter at contra-variant positions.

> (dimap_(F)) :: (b -> a) -> (a -> b) -> F a -> F b

The |Func| example can now be completed with the use of a |dimap|.

> (dimap_(Func)) :: (b -> a) -> (a -> b) -> Func a -> Func b
> (dimap_(Func)) g f func = f `comp` func `comp` g

The functor laws also generalize to the extended functor |dimap|:

> (dimap_(F)) id id = id
> (dimap_(F)) g1 g2 `comp` (dimap_(F)) f1 f2 = (dimap_(F)) (f1 `comp` g1) (g2 `comp` f2)

Note how the first function is contra-variant and the second covariant in the result type when doing composition.

Such a |dimap| can be defined for the typing functor |tyF| using the following functor-indexed function:

> (dimap_(tyF)) :: (a -> b) -> (b -> a) -> (tyF_(b)) -> (tyF_(a))
> (dimap_(tyI))                   con cov x = cov x
> (dimap_(T))                     con cov x = x
> (dimap_(tyF_(a) -> (tyF_(r))))  con cov f = (dimap_(tyF_(r))) con cov `comp` f `comp` (dimap_(tyF_(a))) cov con

At the hole position the covariant function is applied to manipulate the hole value. For constant types |T| the |dimap| is just the identity function. Most interesting is the case for function space, which recursively transforms the argument and result of the function, but with the argument functions |con| and |cov| switched for the contra-variant call. Switching these functions 'flips' the type signature of the function from |(tyF_(b)) -> (tyF_(a))| to |(tyF_(a)) -> (tyF_(b))|.

\paragraph{Typing Functor}
Showing that the typing functor is an actual functor can now be done by showing that the |dimap| constructed for the typing functor preserves the functor laws: identity and composition. The identity law follows readily from the definition of |dimap| and induction on the typing functor. The functor law for composition also follows from induction on the typing functor, the only non-trival case here is the function case, which can be shown using equational reasoning:

>  (dimap_(tyF_(a) -> (tyF_(r)))) g1 g2 `comp` (dimap_(tyF_(a) -> (tyF_(r)))) f1 f2
>`beq` { Eta expansion }
>  \x. ((dimap_(tyF_(a) -> (tyF_(r)))) g1 g2 `comp` (dimap_(tyF_(a) -> (tyF_(r)))) f1 f2) x
>`beq` { Definition composition }
>  \x. (dimap_(tyF_(a) -> (tyF_(r)))) g1 g2 ((dimap_(tyF_(a) -> (tyF_(r)))) f1 f2 x)
>`beq` { Definition dimap }
>  (dimap_(tyF_(r))) g1 g2 `comp` ((dimap_(tyF_(r))) f1 f2 `comp` x `comp` (dimap_(tyF_(a))) f2 f1) `comp` (dimap_(tyF_(a))) g2 g1
>`beq` { Associativity composition }
>  ((dimap_(tyF_(r))) g1 g2 `comp` (dimap_(tyF_(r))) f1 f2) `comp` x `comp` ((dimap_(tyF_(a))) f2 f1 `comp` (dimap_(tyF_(a)) g2 g1))
>`beq` { Induction hypothesis }
>  (dimap_(tyF_(r))) (g2 `comp` f2) (f1 `comp` g1) `comp` x `comp` (dimap_(tyF_(a))) (f1 `comp` g1) (g2 `comp` f2)
>`beq` { Definition dimap }
>  (dimap_(tyF_(a) -> (tyF_(r)))) (f1 `comp` g1) (g2 `comp` f2) x
>`beq` { Eta redutcion }
>  (dimap_(tyF_(a) -> (tyF_(r)))) (f1 `comp` g1) (g2 `comp` f2)

Thus the typing functor is a proper functor.