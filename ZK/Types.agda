open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_; _≢_)

module ZK.Types where

-- Minimal interface needed for cyclic group + base field
record Cyclic-group (G ℤq : Type) : Type where
  infix 6 _^_
  infixl 5 _·_ _/_ _*_
  infixl 4 _+_ _-_
  infix 2 _==_
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
    ·-/  : ∀ {P Q} → P ≡ (P · Q) / Q
    /-/  : ∀ {P Q} → P ≡ Q / (Q / P)
    cancels-/ : ∀ {P Q R} → (P · Q) / (P · R) ≡ Q / R
    /-inj : ∀ {P Q R} → P / R ≡ Q / R → P ≡ Q
    ^-inj : ∀ {b x y} → b ^ x ≡ b ^ y → x ≡ y
    left-*-to-right-/ : ∀ {x y z} → x * y ≡ z → x ≡ (z * modinv y)

    -- This one is not known to be efficiently computable on the groups
    -- which are considered to be secure. However, so far this map
    -- could do anything, such as "dlog x = 0", the dlog-ok is declared
    -- irrelevant and thus prevents from being extracted.
    -- The base is 'b'
    dlog : (b : G) → G → ℤq

    -- This leading dot makes this field irrelevant, hence suggesting
    -- that dlog cannot be extracted or computed.
    .dlog-ok : (b y : G) → b ^ dlog b y ≡ y
