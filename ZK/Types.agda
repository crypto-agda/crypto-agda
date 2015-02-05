open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_)

module ZK.Types where

-- Minimal interface needed for cyclic group + base field
record Cyclic-group (G ℤq : Type) : Type where
  field
    g    : G
    _^_  : G  → ℤq → G
    _·_  : G  → G  → G
    _/_  : G  → G  → G
    _+_  : ℤq → ℤq → ℤq
    _-_  : ℤq → ℤq → ℤq
    _*_  : ℤq → ℤq → ℤq
    modinv : ℤq → ℤq
    _==_ : (x y : G) → Bool

record Cyclic-group-properties {G ℤq} (cg : Cyclic-group G ℤq) : Type where
  open Cyclic-group cg
  field
    ✓-== : ∀ {x y} → x ≡ y → ✓ (x == y)
    ==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y
    ^-+  : ∀ {b x y} → b ^(x + y) ≡ (b ^ x) · (b ^ y)
    ^-*  : ∀ {b x y} → b ^(x * y) ≡ (b ^ x) ^ y
    ^--  : ∀ {b x y} → b ^(x - y) ≡ (b ^ x) / (b ^ y)
    *--  : ∀ {x y z} → x * (y - z) ≡ (x * y) - (x * z)
    /-·  : ∀ {P Q} → P ≡ (P / Q) · Q
    cancels-/ : ∀ {P Q R} → (P · Q) / (P · R) ≡ Q / R
    ^-inj : ∀ {b x y} → b ^ x ≡ b ^ y → x ≡ y
    left-*-to-right-/ : ∀ {x y z} → x * y ≡ z → x ≡ (z * modinv y)
