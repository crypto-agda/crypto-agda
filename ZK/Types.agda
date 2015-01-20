open import Type
open import Data.Bool.Minimal

module ZK.Types where

-- Minimal interface needed for cyclic group + base field
record Cyclic-group (G ℤq : ★) : ★ where
  field
    g    : G
    _^_  : G  → ℤq → G
    _·_  : G  → G  → G
    _/_  : G  → G  → G
    _+_  : ℤq → ℤq → ℤq
    _*_  : ℤq → ℤq → ℤq
    _==_ : (x y : G) → Bool
