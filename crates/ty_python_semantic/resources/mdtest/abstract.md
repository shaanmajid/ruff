# Tests regarding abstract classes

## Instantiation is forbidden

<!-- snapshot-diagnostics -->

Classes with unimplemented abstract methods cannot be instantiated. Type checkers are expected to
detect possible attempts to instantiate abstract classes:

```py
import abc
from typing import Protocol

class Foo(abc.ABC):
    @abc.abstractmethod
    def bar(self): ...

class Spam(Foo): ...

# error: [call-non-callable] "Cannot instantiate `Spam` with unimplemented abstract method `bar`"
Spam()

class Foo2(abc.ABC):
    @abc.abstractmethod
    def bar(self): ...
    @abc.abstractmethod
    def bar2(self): ...

# error: [call-non-callable] "Cannot instantiate `Foo2` with unimplemented abstract methods `bar` and `bar2`"
Foo2()

class Spam2(Foo2): ...

# error: [call-non-callable]
Spam2()

class Foo3(Protocol):
    def bar(self) -> int: ...

class Spam3(Foo3): ...

# error: [call-non-callable]
Spam3()
```
