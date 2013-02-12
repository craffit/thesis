The research in this work presents a formal system for program transformation on a very high level, but a lot of work still needs to be done before this idea can be applied in the real world. The work that still has to be done can roughly be separated into three main areas: extensions for the object language, extensions of the transformation system itself and working toward an implementation. The upcoming sections will highlight some questions that may be beneficial to each of these areas.

\section{Language Extensions}
Although the most vital language extensions of recursion and polymorphism are covered in this work, there are many more features which exist in real-world programming language. How each of these features can be adapted to work with type-and-transform systems is a big source of future work.

\paragraph{Parametrized datatypes}
Most functional programming languages allow types to be parametrized by other types. This poses two important challenges. First off, types may be changed within the parameters of a parametrized data type. Furthermore, one would want to change parametrizable types, such as the |List a| and |Stream a| in the stream fusion example. In this case the |List| should be changed to a |Stream| regardless of the type parameter.

How transformations for such datatypes can be done and for what datatypes the semantics can be preserved is still an open question. Data types can have many features in themselves, such as nested data types and GADTs and it is not clear how these features interact with the type-and-transform system. It could be that simply maintaining the retraction property is enough to guarantee the equivalence properties on such datatypes, but this is not yet proven.

\paragraph{Type Classes}
Type classes language feature allow the implementation of polymorphic functions to be determined by the type with which they are used. Changing a type here would change behaviour of the polymorphic function, something which does usually not happen. How to account for this in the context of type-and-transform systems has yet to be researched.

\paragraph{Let-polymorphism proof}
Although we did a proof by handwaving for the let-polymorphic lambda calculus, this proof should also be formalized. Johann and Voigtländer ~\cite{johann09} give a logical relation for Haskell's underlying base language Core, which is based on the polymorphic lambda calculus. Based on this work it should be possible to prove or disprove the correctness of the let-polymorphic type-and-transform system.

\section{Transformation System Extensions}
\paragraph{Generic Transformation System}
We have seen that a type-and-transform system can readily be derived from the object language, as long as it has a typing system and has well-defined deduction rules. It may be possible to mathematically formulate the mechanism with which a type-and-transform system can be constructed. This would require a structural characterization of the eligible object languages and a procedure with which the type-and-transform system can be derived. This might even lead to a generic proof of correctness for all derivable programming languages.

\paragraph{Transforming Multiple Types}
The type-and-transform system presented in this work is limited to the transformation of one type only. It would be interesting to research the possibility of changing multiple types at once. One way this extension could be done is by allowing multiple source types for one result type. This would allow a wider class of transformations, in which multiple types can be transformed into one type. For example, unifying all string types in a program to one representation.

Another way to allow multiple types to be transformed is by having multiple source-result type pairs. This could be beneficial for composing multiple independent transformations together into one simultaneous transformation pass, or rewriting functions involving multiple transformed types.

In both these extensions the interaction between type changes and transformation has to be carefully researched. The mayor question here is if, and how, the concept of retracts can be generalized to multiple types.

\section{Implementation}
When looking at the implementation of type-and-transform systems there are two main topics to be researched: developing efficient algorithms for transformation and integrating the transformation system into existing infrastructure in a user-friendly and maintainable way.

\paragraph{Efficient implementation}
Naively generating all possible transformation results will result in a slow transformation system. Developing efficient algorithms and heuristics is of essential importance for a real-world application. Not only should transformation be fast, but transformation should also produce the 'best' of all possible results. How to perform good and fast transformations is ongoing research by Sean Leather.

\paragraph{GHC Core-To-Core Transformations}
Recent version of the GHC Haskell compiler allow the user to specify transformation passes. These transformation passes are performed on a typed intermediate language called Core. The Core language is designed to be a simple, desugared functional language upon which optimizations and transformations can be performed, which makes it an ideal candidate for implementation of a type-and-transform system. The Core language has some specific characteristics such as type coercions which should first be researched in the context of type-and-transform systems.

\paragraph{Monoid Transformation}
The monoid transformation could implemented as a separate transformation to optimize the evaluation of monoidal structures. The monoidal transformation can take an arbitrary binary operation and transform a program such that the binary operator is only applied to its left or right argument. A simple user annotation could specify in which way the application nesting should be transformed, such as a fixity declaration:

> infixl 5 (++)
