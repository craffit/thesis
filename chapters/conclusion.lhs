In this work we have presented a formal system for type-changing program transformations. The transformation system is build on top of the simply typed lambda calculus and allows the transformation of a single type into another type while rewriting the operations involving those types. Keeping track of type changes is done by typing the source and result simultaneously using the typing functor, which represents type changes in the programs with a special 'hole' construction. The system has been mechanically proven in Agda to preserve the semantics of the source program after transformation.

\paragraph{}

Although the simply typed lambda calculus may seem too simple to represent a real-world language, it shows that the type-and-transform system can deal with essentials of functional programming: abstraction and application. We are confident that type-and-transform systems and the simultaneous typing technique using typing functors can be readily adapted to more advanced language features, of which we have shown fixed-point recursion and polymorphism.

\paragraph{}

We argue that type-and-transform systems form a solid yet simple paradigm to construct and prove program transformations. Because the transformation rules and typing functor are simply derived from the underlying object language the transformation system can be easily understood.

\paragraph{}

What the performance of real-world implementations of the type-and-transform systems will be has yet to be seen. The system will ultimately rely on some form of proof search which can be slow to compute. Whether this will be a problem can only be found out by making an implementation.