Copy from 1lab.

```agda
module Type where
```

# Universes

A **universe** is a type whose inhabitants are types. In Agda, there is
a family of universes, which, by default, is called `Set`. Rather
recently, Agda gained a flag to make `Set` not act like a keyword, and
allow renaming it in an import declaration from the `Agda.Primitive`
module.

```agda
open import Prim.Type public -- hiding (Prop) public
```

`Type`{.Agda} is a type itself, so it's a natural question to ask: does
it belong to a universe? The answer is _yes_. However, Type can not
belong to itself, or we could reproduce Russell's Paradox, as is done
[in this module].

[in this module]: agda://1Lab.Counterexamples.Russell

To prevent this, the universes are parametrised by a _`Level`{.Agda}_,
where the collection of all `ℓ`-sized types is `Type (lsuc ℓ)`:

```agda
_ : (ℓ : Level) → Type (lsuc ℓ)
_ = λ ℓ → Type ℓ

level-of : {ℓ : Level} → Type ℓ → Level
level-of {ℓ} _ = ℓ
```

## Built-in Types

We re-export the following very important types:

```agda
open import Prim.Data.Sigma public
open import Prim.Data.Bool public
open import Prim.Data.Nat public -- hiding (_<_) public
```

Additionally, we define the empty type:

```agda
data ⊥ : Type where

absurd : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
absurd ()
```

The non-dependent product type `_×_`{.Agda} can be defined in terms of
the dependent sum type:

```agda
_×_ : ∀ {a b} → Type a → Type b → Type _
A × B = Σ[ _ ∈ A ] B

infixr 4 _×_
```

## Lifting

There is a function which lifts a type to a higher universe:

```agda
record Lift {a} ℓ (A : Type a) : Type (a ⊔ ℓ) where
  constructor lift
  field
    lower : A
```

<!--
```agda
instance
  Lift-instance : ∀ {ℓ ℓ′} {A : Type ℓ} → ⦃ A ⦄ → Lift ℓ′ A
  Lift-instance ⦃ x ⦄ = lift x
```
-->

## Function composition

Since the following definitions are fundamental, they deserve a place in
this module:

```agda
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (x : A) → B x → Type ℓ₃}
    → (∀ {x} → (y : B x) → C x y)
    → (f : ∀ x → B x)
    → ∀ x → C x (f x)
f ∘ g = λ z → f (g z)

infixr 40 _∘_

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x
{-# INLINE id #-}

infixr -1 _$_ -- _$ₛ_

_$_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} → ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

{-
_$ₛ_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → SSet ℓ₂} → ((x : A) → B x) → ((x : A) → B x)
f $ₛ x = f x
{-# INLINE _$ₛ_ #-}
-}
```

<!--
```
open import Prim.Literals public

Type∙ : ∀ ℓ → Type (lsuc ℓ)
Type∙ _ = Σ _ id

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → ⊥
infix 3 ¬_
```
-->
