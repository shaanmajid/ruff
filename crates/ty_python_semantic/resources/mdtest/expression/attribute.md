# Attribute access

## Boundness

```py
def _(flag: bool):
    class A:
        always_bound: int = 1

        if flag:
            union = 1
        else:
            union = "abc"

        if flag:
            union_declared: int = 1
        else:
            union_declared: str = "abc"

        if flag:
            possibly_unbound: str = "abc"

    reveal_type(A.always_bound)  # revealed: int

    reveal_type(A.union)  # revealed: Unknown | Literal[1, "abc"]

    reveal_type(A.union_declared)  # revealed: int | str

    # error: [possibly-missing-attribute] "Attribute `possibly_unbound` may be missing on class `A`"
    reveal_type(A.possibly_unbound)  # revealed: str

    # error: [unresolved-attribute] "Class `A` has no attribute `non_existent`"
    reveal_type(A.non_existent)  # revealed: Unknown
```

## Attribute access on union types

When accessing an attribute on a union type where some elements completely lack the attribute, we
emit an error (not a warning), because this is a definite type error - accessing that attribute will
fail for some values in the union at runtime.

This is consistent with how we handle subscripting and iteration on union types.

```py
def f(x: list[int] | None, y: None):
    # error: [not-subscriptable]
    x[0]
    # error: [not-subscriptable]
    y[0]

    # error: [not-iterable]
    for z in x:
        ...
    # error: [not-iterable]
    for z in y:
        ...

    # Attribute access on a union where some elements lack the attribute should also be an error
    # error: [unresolved-attribute] "Attribute `index` is not defined on `None` in union `list[int] | None`"
    x.index
    # error: [unresolved-attribute] "Object of type `None` has no attribute `index`"
    y.index
```

Type aliases of unions should also emit errors for missing attributes:

```toml
[environment]
python-version = "3.12"
```

```py
type MaybeList = list[int] | None

def g(x: MaybeList):
    # error: [unresolved-attribute] "Attribute `index` is not defined on `None` in union `MaybeList`"
    x.index
```
