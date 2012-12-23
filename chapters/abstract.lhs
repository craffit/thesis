Program transformations play a central role in the construction of compilers. Before a source program comes out as machine readable instructions, it has gone through a lot of optimization and simplification steps, preferably without changing the behavior of the original program.

Traditionally, these transformations work by manipulating the syntactic constructs of a language, and do not alter the types of a program, or are applied to untyped sources. However, in recent years there has been an increasing interest in transformations in type-changing program transformations on typed sources: transformations in which it is possible to change the types together with the terms. 

This work introduces an extensible transformation system based on the simply typed lambda calculus, which allows type-changing transformations between terms. The system ensures that a transformation preserves the semantics of the source term, independent of the concrete datatypes and evaluation strategy of the underlying lambda calculus. This statement is formally proven using logical relations and mechanically verified in the dependently typed programming language Agda. Central to the transformation system is the concept of typing functors, a construction which types the source and result of a transformation simultaneously, while allowing changes in types to occur.
