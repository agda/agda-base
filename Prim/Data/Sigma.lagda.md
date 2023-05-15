Modified copy from 1lab.

```agda
open import Prim.Type

module Prim.Data.Sigma where
```

# Primitives: Sigma types

The dependent sum type, total space, or type of dependent pairs, is
defined as a record, so that it enjoys definitional η.

```agda
open import Agda.Builtin.Sigma public
  using (fst; snd)
  renaming (Σ to infix 5 Σ
           ;_,_ to infixr 4 _,_)

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : {a b : Level} → (A : Type a) → (A → Type b) → Type (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

Similarly, for the unit type:

```agda
open import Agda.Builtin.Unit public
  using (⊤; tt)
```
