------------------------------------------------------------------------
-- From the Agda standard library
--
-- Simple combinators working solely on and with functions
-- (REMOVED more specialized operations)
------------------------------------------------------------------------

-- The contents of this module is also accessible via the `Function`
-- module. See `Function.Strict` for strict versions of these
-- combinators.

module Function.Base where

open import Level using (Level)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

const : A → B → A
const x = λ _ → x

constᵣ : A → B → B
constᵣ _ = id

------------------------------------------------------------------------
-- Operations on dependent functions

-- These are functions whose output has a type that depends on the
-- value of the input to the function.

infixr 9 _∘_ _∘₂_
infixl 0 _|>_
infix  0 case_return_of_
infixr -1 _$_

-- Composition

_∘_ : ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-} -- DECIDE (also below)

_∘₂_ : ∀ {A₁ : Set a} {A₂ : A₁ → Set d}
         {B : (x : A₁) → A₂ x → Set b}
         {C : {x : A₁} → {y : A₂ x} → B x y → Set c} →
       ({x : A₁} → {y : A₂ x} → (z : B x y) → C z) →
       (g : (x : A₁) → (y : A₂ x) → B x y) →
       ((x : A₁) → (y : A₂ x) → C (g x y))
f ∘₂ g = λ x y → f (g x y)

-- Flipping order of arguments

flip : ∀ {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- Category.Functor._<$>_ from Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

-- Flipped application (aka pipe-forward)

_|>_ : ∀ {A : Set a} {B : A → Set b} →
       (a : A) → (∀ a → B a) → B a
_|>_ = flip _$_
{-# INLINE _|>_ #-}

λ- : ∀ {A : Set a} {B : A → Set b} → ({x : A} → B x) → ((x : A) → B x)
λ- f = λ x → f
{-# INLINE λ- #-}

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_return_of_ : ∀ {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x return B of f = f x
{-# INLINE case_return_of_ #-}

------------------------------------------------------------------------
-- Non-dependent versions of dependent operations

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.

infixr 9 _∘′_ _∘₂′_
infixl 0 _|>′_
infix  0 case_of_
infixr -1 _$′_

-- Composition

_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

_∘₂′_ : (C → D) → (A → B → C) → (A → B → D)
f ∘₂′ g = _∘₂_ f g

-- Flipping order of arguments

flip′ : (A → B → C) → (B → A → C)
flip′ = flip

-- Application

_$′_ : (A → B) → (A → B)
_$′_ = _$_

-- Flipped application (aka pipe-forward)

_|>′_ : A → (A → B) → B
_|>′_ = _|>_

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_of_ : A → (A → B) → B
case x of f = case x return _ of f
{-# INLINE case_of_ #-}

------------------------------------------------------------------------
-- Operations that are only defined for non-dependent functions

infixl 1 _⟨_⟩_
infixl 0 _∋_

-- Binary application

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.

_∋_ : (A : Set a) → A → A
A ∋ x = x

-- Conversely it is sometimes useful to be able to extract the
-- type of a given expression.

typeOf : {A : Set a} → A → Set a
typeOf {A = A} _ = A

-- Construct an element of the given type by instance search.

it : {A : Set a} → {{A}} → A
it {{x}} = x