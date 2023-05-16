<!--
```agda
-- open import 1Lab.Type.Sigma
-- open import 1Lab.Equiv
-- open import 1Lab.Path
open import Type

open import Data.Product.NAry
open import Data.Product hiding (_<*>_)
open import Data.Vec.Base hiding ([_])
open import Data.Bool
open import Data.List hiding ([_])
```
-->

```agda
module Reflection where

open import Prim.Data.String public
open import Prim.Data.Float public
open import Prim.Data.Maybe public
open import Data.Maybe.Base -- using (maybe→alt) public
open import Prim.Data.Word public
-- open import Meta.Traverse public
open import Meta.Idiom public
open import Meta.Bind public
open import Meta.Alt public
open import Meta.Traverse public

-- open Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate) public
-- open Data.Product.NAry using ([_]) public
-- open Data.List public
-- open Data.Bool public
```

# Metaprogramming

Here, we bind and define helpers for Agda's clunky metaprogramming
facilities.

## QNames

The "Q" is for **q**ualified.

```agda
open import Agda.Builtin.Reflection public
  hiding (Type)

-- from end of Reflection.lagda.md in 1lab
instance
  Map-TC : Map (eff TC)
  Map-TC .Map._<$>_ f x = bindTC x λ x → returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .Idiom.pure = returnTC
  Idiom-TC .Idiom._<*>_ f g = bindTC f λ f → bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC .Bind._>>=_ = bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .Alt.fail′ xs = typeError [ strErr xs ]
  Alt-TC .Alt._<|>_ = catchTC
```
</details>

# Reflection helpers

```agda
argH0 argH argN : ∀ {ℓ} {A : Type ℓ} → A → Arg A
argH = arg (arg-info hidden (modality relevant quantity-ω))
argH0 = arg (arg-info hidden (modality relevant quantity-0))
argN = arg (arg-info visible (modality relevant quantity-ω))

Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

underAbs : ∀ {ℓ} {A : Type ℓ} → Term → TC A → TC A
underAbs (lam v (abs nm _)) m = extendContext nm (arg (arg-info v (modality relevant quantity-ω)) unknown) m
underAbs (pi a (abs nm _)) m = extendContext nm a m
underAbs _ m = m

new-meta : Term → TC Term
new-meta ty = do
  mv ← checkType unknown ty
  debugPrint "tactic.meta" 70
    [ strErr "Created new meta " , termErr mv , strErr " of type " , termErr ty ]
  pure mv

new-meta′ : Term → TC (Meta × Term)
new-meta′ ty = do
  tm@(meta mv _) ← checkType unknown ty
    where _ → typeError $ [ strErr "impossible new-meta′" ]
  debugPrint "tactic.meta" 70
    [ strErr "Created new meta " , termErr tm , strErr " of type " , termErr tm ]
  pure (mv , tm)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

pattern _v∷_ t xs = arg (arg-info visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arg-info hidden (modality relevant quantity-ω)) t ∷ xs
pattern _hm∷_ t xs = arg (arg-info hidden (modality relevant _)) t ∷ xs

infixr 30 _v∷_ _h∷_ _hm∷_

infer-hidden : Nat → List (Arg Term) → List (Arg Term)
infer-hidden zero xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

getName : Term → Maybe Name
getName (def x _) = just x
getName (con x _) = just x
getName _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

_visibility=?_ : Visibility → Visibility → Bool
visible visibility=? visible = true
hidden visibility=? hidden = true
instance′ visibility=? instance′ = true
_ visibility=? _ = false

-- [TODO: Reed M, 06/05/2022] We don't actually use any fancy modalities
-- anywhere AFAICT, so let's ignore those.
_arg-info=?_ : ArgInfo → ArgInfo → Bool
arg-info v₁ m₁ arg-info=? arg-info v₂ m₂ = (v₁ visibility=? v₂)

arg=? : ∀ {a} {A : Type a} → (A → A → Bool) → Arg A → Arg A → Bool
arg=? eq=? (arg i₁ x) (arg i₂ y) = andᵇ (i₁ arg-info=? i₂) (eq=? x y)

-- We want to compare terms up to α-equivalence, so we ignore binder
-- names.
abs=? : ∀ {a} {A : Type a} → (A → A → Bool) → Abs A → Abs A → Bool
abs=? eq=? (abs _ x) (abs _ y) = eq=? x y

{-# TERMINATING #-}
-- [TODO: Reed M, 06/05/2022] Finish this

_term=?_ : Term → Term → Bool
var nm₁ args₁ term=? var nm₂ args₂ = andᵇ (nm₁ ≡ᵇ nm₂) (all=? (arg=? _term=?_) args₁ args₂)
con c₁ args₁ term=? con c₂ args₂ = andᵇ (c₁ name=? c₂) (all=? (arg=? _term=?_) args₁ args₂)
def f₁ args₁ term=? def f₂ args₂ = andᵇ (f₁ name=? f₂) (all=? (arg=? _term=?_) args₁ args₂)
lam v₁ t₁ term=? lam v₂ t₂ = andᵇ (v₁ visibility=? v₂) (abs=? _term=?_ t₁ t₂)
pat-lam cs₁ args₁ term=? pat-lam cs₂ args₂ = false
pi a₁ b₁ term=? pi a₂ b₂ = andᵇ (arg=? _term=?_ a₁ a₂) (abs=? _term=?_ b₁ b₂)
agda-sort s term=? t₂ = false
lit l term=? t₂ = false
meta x x₁ term=? t₂ = false
unknown term=? t₂ = false
_ term=? _ = false


instance
  String-ErrorPart : IsString ErrorPart
  String-ErrorPart .IsString.Constraint _ = ⊤
  String-ErrorPart .IsString.fromString s = strErr s

{-
“refl” : Term
“refl” = def (quote refl) []
-}

wait-for-args : List (Arg Term) → TC (List (Arg Term))
wait-for-type : Term → TC Term

wait-for-type (var x args) = var x <$> wait-for-args args
wait-for-type (con c args) = con c <$> wait-for-args args
wait-for-type (def f args) = def f <$> wait-for-args args
wait-for-type (lam v (abs x t)) = pure (lam v (abs x t))
wait-for-type (pat-lam cs args) = pure (pat-lam cs args)
wait-for-type (pi (arg i a) (abs x b)) = do
  a ← wait-for-type a
  b ← wait-for-type b
  pure (pi (arg i a) (abs x b))
wait-for-type (agda-sort s) = pure (agda-sort s)
wait-for-type (lit l) = pure (lit l)
wait-for-type (meta x x₁) = blockOnMeta x
wait-for-type unknown = pure unknown

wait-for-args [] = pure []
wait-for-args (arg i a ∷ xs) = ⦇ ⦇ (arg i) (wait-for-type a) ⦈ ∷ wait-for-args xs ⦈

wait-just-a-bit : Term → TC Term
wait-just-a-bit (meta m _) = blockOnMeta m
wait-just-a-bit tm = pure tm


```

## Debugging Tools

```agda
debug! : ∀ {ℓ} {A : Type ℓ} → Term → TC A
debug! tm = typeError (strErr "[DEBUG]: " ∷ termErr tm ∷ [])

quote-repr-macro : ∀ {ℓ} {A : Type ℓ} → A → Term →  TC ⊤
quote-repr-macro a hole = do
  tm ← quoteTC a
  repr ← quoteTC tm
  typeError $ strErr "The term\n  "
    ∷ termErr tm
    ∷ strErr "\nHas quoted representation\n  "
    ∷ termErr repr ∷ []

macro
  quote-repr! : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr! a = quote-repr-macro a

instance
  IsString-Error : IsString (List ErrorPart)
  IsString-Error .IsString.Constraint _ = ⊤
  IsString-Error .fromString s = fromString s ∷ []

unify-loudly : Term → Term → TC ⊤
unify-loudly a b = do
  debugPrint "tactic" 50 $ termErr a ∷ strErr " =? " ∷ termErr b ∷ []
  unify a b

print-depth : String → Nat → Nat → List ErrorPart → TC ⊤
print-depth key level nesting es = debugPrint key level $
  strErr (nest nesting ("[" <> primShowNat nesting <> "]  ")) ∷ es
  where
    _<>_ : String → String → String
    _<>_ = primStringAppend
    infixr 10 _<>_

    nest : Nat → String → String
    nest zero s = s
    nest (suc x) s = nest x (s <> "  ")

```
