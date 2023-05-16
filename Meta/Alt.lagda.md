<!--
```agda
open import Type
open import Data.String

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module Meta.Alt where
```

```agda
record Alt (M : Effect) : Typeω where
  private module M = Effect M
  field
    fail′ : ∀ {ℓ} {A : Type ℓ} → String → M.₀ A
    _<|>_ : ∀ {ℓ} {A : Type ℓ} → M.₀ A → M.₀ A → M.₀ A
  infixl 3 _<|>_

  fail : ∀ {ℓ} {A : Type ℓ} → M.₀ A
  fail = fail′ "Alt: empty error message"

  _<?>_ : ∀ {ℓ} {A : Type ℓ} → M.₀ A → String → M.₀ A
  what <?> why = what <|> fail′ why

open Alt ⦃ ... ⦄ public

guard
  : ∀ {M : Effect} (let module M = Effect M) ⦃ appl : Idiom M ⦄ ⦃ alt : Alt M ⦄
  → Bool → M.₀ ⊤
guard true = pure tt
guard false = fail

guardM
  : ∀ {M : Effect} (let module M = Effect M) ⦃ mon : Bind M ⦄ ⦃ alt : Alt M ⦄
  → M.₀ Bool → M.₀ ⊤
guardM M = M >>= guard
```
