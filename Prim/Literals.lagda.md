<!--
```agda
open import Prim.Data.Sigma
open import Prim.Data.Nat
open import Prim.Type
```
-->

```agda
module Prim.Literals where
```

# Primitive: Overloaded literals

We define the records `Number`{.Agda}, `Negative`{.Agda} and
`String`{.Agda} to allow overloading of the numeric literals.

```agda
open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)
open import Data.Unit public

open import Agda.Builtin.String public

-- Natural number literals for ℕ

open import Agda.Builtin.Nat renaming (Nat to ℕ)

instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = record { Constraint = λ _ → Unit ; fromNat = λ n → n }

-- from 1lab

record IsString {a} (A : Type a) : Type (lsuc a) where
  field
    Constraint : String → Type a
    fromString : (s : String) {{_ : Constraint s}} → A

open IsString {{...}} public using (fromString)

```
