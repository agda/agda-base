Slightly modified copy from the 1lab.

```agda
module Prim.Type where
```

# Primitives: Sorts

This module defines bindings for the primitive sorts in Agda. These are
_very magic_ symbols since they bootstrap everything about the type
system. For more details about the use of universes, see
[`1Lab.Type`](1Lab.Type.html).

```agda
```

Additionally, we have the `Level` type, of _universe levels_. The
universe levels are an algebra containing 0, closed under successor and
maximum. The difference between this and e.g. the natural numbers is
that `Level` isn't _initial_, i.e. you can't pattern-match on it.

```agda
open import Agda.Primitive public
  using    ( Level
           ; lzero
           ; lsuc
           ; _⊔_
           )
  renaming (Set to Type
           ; Setω to Typeω)
```
