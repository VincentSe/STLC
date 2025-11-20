# STLC
Simply typed lambda calculus, proved in Rocq.

We define lambda-terms, their types and prove strong normalization by Tait's method. Lambda-types do not have explicit type annotations, this is Curry-style STLC. Also, we assume only one base type, `Bot`, that has no constant terms in it. This makes the calculus polymorphic : if a term `t` has type `tau`, then `t` also has type `ext tau alpha`, where `alpha` is any type and `ext tau alpha` substitutes `alpha` into every `Bot` leaf of `tau`.

File `LambdaCalculusCore.v` contains untyped lambda calculus. Alpha conversion is handled by De Bruijn indices.

File `LambdaCalculusType.v` defines types and proves strong normalization of typed terms.

File `LambdaCalculusProg.v` defines the usual Church encodings of data types, like booleans, integers and lists.
