<!--
```agda
open import Prim.Type
```
-->

```agda
module Prim.Data.Maybe where
```

# Primitive: The Maybe type

The `Maybe`{.Agda} is the free pointed type on a given type. It is used
by Agda's primitives to represent failure.

```agda
open import Agda.Builtin.Maybe public
  using (Maybe; just; nothing)
```
