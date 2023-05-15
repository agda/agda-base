<!--
```agda
open import Prim.Data.Bool
open import Prim.Type
```
-->

```agda
module Prim.Data.Nat where
```

# Primitive: Natural numbers

The [natural numbers](Data.Nat.html) are the h-initial type generated by
a point and an endomorphism.

```agda
open import Agda.Builtin.Nat public
  using (Nat)
  renaming (_+_ to infixl 6 _+_
           ;_-_ to infixl 6 _-_
           ;_*_ to infixl 7 _*_
           ;_==_ to infix  4 _==_
           ;_<_ to infix  4 _<_
           )
```

## Optimised functions on Nat

Agda lets us define the following functions on natural numbers, which
are computed more efficiently when bound as `BUILTIN`s.