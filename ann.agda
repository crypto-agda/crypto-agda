module ann where

import Level

record Ann {a b} {A : Set a} (ann : A) (B : Set b) : Set b where
  constructor mk
  field
    get : B
