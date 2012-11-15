\section{Functors}
A functor can be seen as a function on types. It takes as parameter a type and yields a 
new type based on its argument. Associated with a type level functor is a term level functor which 
lifts functions on the type parameter to functions on the functor:

> type F a
> fmap :: (a -> b) -> F a -> F b

For |fmap| to be a proper term-level functor it has to obey the functor laws:

> fmap id = id
> fmap g `comp` fmap f = fmap (g `comp` f)

A list is an example of a Functor in Haskell:

> data List a = Nil | Cons a (List a)
> fmap :: (a -> b) -> List a -> List b
> fmap _ Nil         = Nil
> fmap f (Cons a l)  = Cons (f a) (fmap f l)

What makes functors special, is that an implementation for the term level function |fmap| can 
be constructed from the functor type. This is what makes functors useful for our purpose. We
can reason about the semantics of the terms by knowing the types.

For normal functors we can only construct a term-level functor when the argument type
occurs in covariant positions within the datatype. This means we can construct |fmap| for all
polynomial types (datatypes without functions), but not for all datatypes containing functions.
However, our typing functor |F| includes a function space constructor, so we will need something more powerful. 

Meijer and Hutton\cite{meijer} showed that it is possible to define functors for function types 
(exponential types) when we use |dimap|s. A |dimap| is the same as as a normal |fmap| but with an extra
function argument which can be used for occurrences of the type parameter at contra-variant
positions. The functor laws also have an extended version for |dimap|s:

> dimap_F :: (a -> b) -> (b -> a) -> F b -> F a

> dimap_F id id = id
> dimap_F g1 g2 `comp` dimap_F f1 f2 = dimap_F (f1 `comp` g1) (g2 `comp` f2)

Note how the first function is contra-variant and the second covariant in the result type. 

Based on this work, we can define how the term-level |dimap| is derived from our typing functor
using the following type-indexed function:

> dimap_F :: (a -> b) -> (b -> a) -> <<F>>b -> <<F>>a
> dimap_Id    rep abs x = abs x
> dimap_T     rep abs x = x
> dimap_F1F2  rep abs f = dimap_F2 rep abs `comp` f `comp` dimap_F1 abs rep

