\subsection{Hughes' Strings}
\label{sec:hughes}
One example of a type-changing program transformation is known as Hughes' lists ~\cite{hughes86}. In his work, Hughes presents a method which reduces the computational overhead induced by the naive implementation of string concatenation. Hughes' method does not only work for strings but for lists in general, but we will use strings for simplicity. To see what problem Hughes' strings solve, consider the standard implementation of string concatenation:

> infixr 5 ++
> (++) :: String -> String -> String
> []       ++ ys = ys
> (x: xs)  ++ ys = x : (xs ++ ys)

The running time of this function is depends on the size of its first argument. The problem with this definition becomes clear when analyzing necessary computations in the following examples:

> s1, s2, s3, s4 :: [Char]
> s1 = "aap" ++ ("noot" ++ "mies")
> s2 = ("aap" ++ "noot") ++ "mies"
> s3 = "aap" ++ "noot" ++ "mies"
> s4 = (\x -> x ++ "mies") ("aap" ++ "noot")

In the first example |"noot"| is traversed to create |"nootmies"|, and consecutively |"aap"| is traversed to create |"aapnootmies"|. The second example is almost identical, but first |"aapnoot"| is constructed by traversing |"aap"| and then |"aapnootmies"| is constructed after traversing |"aapnoot"|. Thus |"aap"| is traversed twice, a gross inefficiency! To partly counter this problem, |(++)| has been made right-associative, such that the third example produces the most optimal result. However, there are still many cases in which concatenation does not work optimal, as in the fourth example.

The Hughes' lists transformation solves this by treating string not as normal string (|String|) but as functions over strings (|String -> String|). Strings now become continuations of strings, where the continuation represents an unfinished string, for which the tail still has to be filled in. Strings and Hughes' strings can be transformed into each other by the functions |(rep_(ss))| and |(abs_(ss))|.

> (rep_(ss)) :: String -> (String -> String)
> (rep_(ss)) ls = (ls ++)
>
> (abs_(ss)) :: (String -> String) -> String
> (abs_(ss)) c = c ""

The speedup comes from the fact that, instead of normal concatenation, function composition can be used to concatenate two Hughes' strings.

> s1, s2, s3, s4 :: String
> s1 = (abs_(ss)) $ (rep_(ss)) "aap" `comp` ((rep_(ss)) "noot" `comp` (rep_(ss)) "mies")
> s2 = (abs_(ss)) $ ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot") `comp` (rep_(ss)) "mies"
> s3 = (abs_(ss)) $ (rep_(ss)) "aap" `comp`  (rep_(ss)) "noot" `comp` (rep_(ss)) "mies"
> s4 = (abs_(ss)) $ (\x -> x `comp` (rep_(ss)) "mies") ((rep_(ss)) "aap" `comp` (rep_(ss)) "noot")

All examples now have the same, optimal running time because the continuation technique avoids building intermediate results: each string is only traversed at most once. Additionally, where the speed of normal concatenation depends on the size of its first argument, function composition has a constant running time.

\subsection{Stream Fusion}
\label{sec:fusion}
Another example of a type-changing program transformation is stream fusion, as found in Coutts et al.~\cite{coutts07}. The goal of stream fusion is the same as Hughes' lists: optimizing operations on lists. Stream fusion does this using a technique called deforestation, which reduces the number of intermediate data structures constructed during evaluation. Consider the following example:

> op :: (Int -> Int) -> [Int] -> [Int]
> op f = map f `comp` filter isEven `comp` map f

When this example is compiled without optimization, an intermediate result will be constructed at the position of each composition. Modern compilers such as GHC can partly optimize this kind of overhead away by changing the internal representation of lists to |Stream|s

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

Note that the |mapS| function is not recursive. It only manipulates the function that works on lists, not the lists themselves. This is what avoids the intermediate result from being constructed. We can now construct an optimized version of our example:

> op :: (Int -> Int) -> [Int] -> [Int]
> op f = (abs_(fs)) `comp` mapS f `comp` filterS isEven `comp` mapS g `comp` (rep_(fs))

The only function constructing a list is |(abs_(fs))|, all other operations are 'fused' together.

\paragraph{Stream fusion in GHC}
The Haskell GHC compiler incorporates a system which can be used to create such optimizations. This system is based on local, type-checked rewrite rules to rewrite terms which can be optimized. This is done for the Stream Fusion optimization by redefining the basic list functions and adding an optimizing rewrite rule in the following way:

> map :: (a -> b) -> [a] -> [b]
> map f = (abs_(fs)) `comp` mapS f `comp` (rep_(fs))
>
> filter :: (a -> Bool) -> [a] -> [a]
> filter f = (abs_(fs)) `comp` filterS f `comp` (rep_(fs))
>
> {-# RULES "rep/abs" rep . abs = id #-}

The |op| example can now be optimized by the compiler, by first expanding and inlining all definitions and consecutively applying the optimization rewrite rule, getting rid of all abs-rep pairs. Thus this achieves a type-changing transformation by applying a non type-changing rewrite rule. However, this system is limited by how much the compiler can inline and replace the terms. It is primarily a syntactic method. To see where optimization may fail, consider the following example:

> op' :: (Int -> Int) -> [Int] -> [Int]
> op' f =  let applyMap = (\x -> map f x)
>          in applyMap `comp` filter isEven `comp` applyMap

When expanding these definitions, this yields the following term

> op' :: (Int -> Int) -> [Int] -> [Int]
> op' f =  let applyMap = (\x -> (abs_(fs)) `comp` mapS f `comp` (rep_(fs)) $ x)
>          in applyMap `comp` (abs_(fs)) `comp` filterS isEven `comp` (rep_(fs)) `comp` applyMap

Without proper inlining, the rep-abs rule can not fire. In this situation the inliner may solve this issue, but there are situations where inlining is not enough to make Stream Fusion work. Allowing direct type changes in the program however, yields the desired result:

> op' :: (Int -> Int) -> [Int] -> [Int]
> op' f =  let applyMap = (\x -> mapS f x)
>          in (abs_(fs)) `comp` applyMap `comp` filterS isEven `comp` applyMap `comp` (rep_(fs))
