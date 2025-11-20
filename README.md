# STLC
Simply typed lambda calculus, proved in Rocq.

File `LambdaCalculusCore.v` contains untyped lambda calculus. Alpha conversion is handled by De Bruijn indices. It proves confluence by the parallel beta-reduction method (Church-Rosser theorem).

File `LambdaCalculusType.v` defines types and proves strong normalization of typed terms, by Tait's method. Lambda-types do not have explicit type annotations, this is Curry-style STLC. Also, we assume no base type, only type variables. This forces to use Church encodings and restrains the expressible integer functions to the extended polynomials. 3 extensions can be considered to express more functions : Gödel's system T, system F and Hindley-Milner. System T adds an ad hoc syntax to compute integers, the other 2 type systems add polymorphism. Hindley-Milner is a restriction of system F to have automatic type inference.

File `LambdaCalculusProg.v` defines the usual Church encodings of data types, like booleans, integers and lists.
