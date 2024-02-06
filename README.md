# constraint-based-type-inference

An Agda formalization of constraint-based type inference for the simply-typed lambda-calculus.

Uses a de Bruijn representation of type variables.
The implementation of the occurs-check follows:

> Conor McBride, First-Order Unification by Structural Recursion, Journal of Functional Programming, 2003.

Type inference is split into a first pass extracting constraints between types,
and a second pass solving the constraints by first-order unification.

Constraint-based type inference has been systematically described by:

> Francois Pottier and Didier Rémy, The Essence of ML Type Inference.
> In B. C. Pierce, Advanced Topics in Types and Programming Languages, The MIT Press, 2004.

So do not expect any new ideas here.  Just enjoy the Agda code!

Limitations (as of 2024-02-06):
- Just specification (judgements), no algorithm (functions).
- Only soundness, no completeness.
- No `let`-generalization / ML-polymorphism.

Tested with:
- Agda 2.6.4.1 and agda-stdlib 2.0

Related work:
- https://github.com/wenkokke/FirstOrderUnificationInAgda
