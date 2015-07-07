open import Type using (Type)
open import Type.Eq
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_; _≢_)
open import Algebra.Group
open import Algebra.Field

module ZK.Types where

-- PoK: (Zero-Knowledge) Proof of Knowledge
-- CP: Chaum-Pedersen
-- EG: ElGamal
-- rnd: Knowledge of the secret, random exponent used in ElGamal encryption
record PoK-CP-EG-rnd (ℤq ℤp★ : Set) : Set where
  inductive -- NO_ETA
  field
    g y α β A B : ℤp★
    m c s : ℤq

-- Minimal interface needed for cyclic group + base field
record Cyclic-group (G ℤq : Type) : Type where
  infix 8 _^_
  field
    ℤq-fld : Field ℤq
    G-grp : Group G
    eq?-G : Eq? G
    g    : G

  open Eq? eq?-G public
  open Field ℤq-fld hiding (_/_; _^_) public
  open Group G-grp renaming (_∙_ to _·_) using (_/_) public

  field
    -- TODO: cleanup
    _^_  : G  → ℤq → G
    ^-+  : ∀ {b x y} → b ^(x + y) ≡ (b ^ x) · (b ^ y)
    ^-*  : ∀ {b x y} → b ^(x * y) ≡ (b ^ x) ^ y
    ^--  : ∀ {b x y} → b ^(x − y) ≡ (b ^ x) / (b ^ y)
    *--  : ∀ {x y z} → x * (y − z) ≡ (x * y) − (x * z)
    /-·  : ∀ {P Q} → P ≡ (P / Q) · Q
    ·-/  : ∀ {P Q} → P ≡ (P · Q) / Q
    /-/  : ∀ {P Q} → P ≡ Q / (Q / P)
    cancels-/ : ∀ {P Q R} → (P · Q) / (P · R) ≡ Q / R
    /-inj : ∀ {P Q R} → P / R ≡ Q / R → P ≡ Q
    ^-inj : ∀ {b x y} → b ^ x ≡ b ^ y → x ≡ y
    left-*-to-right-/ : ∀ {x y z} → x * y ≡ z → x ≡ (z * y ⁻¹)

    -- This one is not known to be efficiently computable on the groups
    -- which are considered to be secure. However, so far this map
    -- could do anything, such as "dlog x = 0", the dlog-ok is declared
    -- irrelevant and thus prevents from being extracted.
    -- The base is 'b'
    dlog : (b : G) → G → ℤq

    -- This leading dot makes this field irrelevant, hence suggesting
    -- that dlog cannot be extracted or computed.
    .dlog-ok : (b y : G) → b ^ dlog b y ≡ y
