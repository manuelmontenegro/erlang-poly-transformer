# Erlang Polymorphic Specs

This tool is meant to improve the precision of Dialyzer when dealing with polymorphic specs. It transforms an Erlang source code program in order to substitute macro calls for polymorphic function calls. The macro call forces Dialyzer to use the concrete monomorphic instance of the spec corresponding to the types of the arguments.

## Example

Given the following definition:
```erlang
-spec id(A) -> A.
id(X) -> X.

f() -> id(0).
```

Without the transformation Dialyzer would use the monomorphic instance `any() -> any()`  when processing the call `id(0)`. That is why `f` would be inferred with the following spec:

```erlang
-spec f() -> any().
```

The transformation would replace the call `id(0)` in `f` with a call to a macro `?ID(0)` that uses the specific instance `0 -> 0`. In this way `f` would be inferred with the following spec:

```erlang
-spec f() -> 0.
```

##Usage

This tool has been implemented as an Erlang compiler phase. In order to perform the transformation add the following directive to your module:

```erlang
-compile({parse_transform, poly_transformer}).
```
The module `poly_transformer` has to be in the same directory in which Dialyzer/Typer is run, or it must be accessible from the Erlang code path. This transformation is only performed when Dialyzer/Typer is running. With an standard compilation no transformation is done.

For instance, given the following module:
```erlang
-module(test).

% Identity function
-spec id(A) -> A.
id(X) -> X.

f() -> id(0).
```
Typer will yield the following output:
```erlang
-spec id(A_1) -> A_1.
-spec f() -> 0.
```

##Transformation Flags
The module being transformed may include the following attributes:

```erlang
-no_polymorphic_schemes([fun1/arity1, fun2/arity2, ...]).
```

It prevents the type specs of the given function definitions from being handled polymorphically. The calls to these functions will not be translated.

```erlang
-no_polymorphic_calls([fun1/arity1, fun2/arity2, ...]).
```

It prevents the calls contained within these functions from being transformed.

```erlang
-poly_transformed_output("filename").
```
It specifies the name of the file containing the transformed program. If not specified, it will add the suffix `_trans` to the name of the source file. For instance, `example.erl` will be transformed into `example_trans.erl`.



