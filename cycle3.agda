{-# OPTIONS --without-K #-}
open import Function.NP
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_])
open import cycle using (here; there; [_]; _∷_)

module cycle3 where

data 𝟛 : Set where
  0₃ 1₃ 2₃ : 𝟛

-- open import Algebra.FunctionProperties.Eq {A = 𝟛}

Fun = 𝟛 → 𝟛

module M (f : Fun) where
  open cycle 𝟛 f public hiding (here; there; [_]; _∷_)

  ↺0 = ↺ 0₃
  ↺1 = ↺ 1₃
  ↺2 = ↺ 2₃
  0↦*1 = 0₃ ↦* 1₃
  0↦*2 = 0₃ ↦* 2₃
  1↦*0 = 1₃ ↦* 0₃
  1↦*2 = 1₃ ↦* 2₃
  2↦*0 = 2₃ ↦* 0₃
  2↦*1 = 2₃ ↦* 1₃

suc₃ : Fun
suc₃ 0₃ = 1₃
suc₃ 1₃ = 2₃
suc₃ 2₃ = 0₃

[01]₃ : Fun
[01]₃ 0₃ = 1₃
[01]₃ 1₃ = 0₃
[01]₃ 2₃ = 2₃

is0₃? : Fun
is0₃? 0₃ = 1₃
is0₃? 1₃ = 0₃
is0₃? 2₃ = 0₃

module Suc₃ where
  open M suc₃
  -- open cycle 𝟛 suc₃ hiding (here; there)

  module L00 where
    c : ↺0
    c = [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl

    0∈c : 0₃ ∈ c
    0∈c = here

    1∉c : 1₃ ∉ c
    1∉c ()

    2∉c : 2₃ ∉ c
    2∉c ()

  module C20 where
    c : 2↦*0
    c = 2₃ ∷ [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = there here

    1∉c : 1₃ ∉ c
    1∉c (there ())

    2∈c : 2₃ ∈ c
    2∈c = here

  module C120 where

    c : 1↦*0
    c = 1₃ ∷ 2₃ ∷ [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there (there ()))
    c-is-chain (there (there ())) here
    c-is-chain (there p) (there q) = ap there (C20.c-is-chain p q)

    0∈c : 0₃ ∈ c
    0∈c = there (there here)

    2∈c : 2₃ ∈ c
    2∈c = there here

  module C0120 where
    c : ↺0
    c = 0₃ ∷ 1₃ ∷ 2₃ ∷ [ 0₃ ]

    0∈c : 0₃ ∈ c
    0∈c = here

    0∈c' : 0₃ ∈ c
    0∈c' = there (there (there here))

    c-no-chain : ¬(is-chain c)
    c-no-chain pf = case pf 0∈c 0∈c' of λ { () }

module [01]₃ where
  open M [01]₃

  module L00 where
    c : ↺0
    c = [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl

    0∈c : 0₃ ∈ c
    0∈c = here

    1∉c : 1₃ ∉ c
    1∉c ()

    2∉c : 2₃ ∉ c
    2∉c ()

  module C10 where
    c : 1↦*0
    c = 1₃ ∷ [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = there here

    1∈c : 1₃ ∈ c
    1∈c = here

    2∉c : 2₃ ∉ c
    2∉c (there ())

  module C01 where
    c : 0↦*1
    c = 0₃ ∷ [ 1₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = here

    1∈c : 1₃ ∈ c
    1∈c = there here

    2∉c : 2₃ ∉ c
    2∉c (there ())

  module L2 where
    c : ↺2
    c = [ 2₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl

    0∉c : 0₃ ∉ c
    0∉c ()

    1∉c : 1₃ ∉ c
    1∉c ()

    2∈c : 2₃ ∈ c
    2∈c = here

  module L010 where
    c : ↺0
    c = 0₃ ∷ 1₃ ∷ [ 0₃ ]

    0∈c : 0₃ ∈ c
    0∈c = here

    0∈c' : 0₃ ∈ c
    0∈c' = there (there here)

    1∈c : 1₃ ∈ c
    1∈c = there here

    2∉c : 2₃ ∉ c
    2∉c (there (there ()))

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 0∈c 0∈c' of λ { () }

  module L101 where
    c : ↺1
    c = 1₃ ∷ 0₃ ∷ [ 1₃ ]

    0∈c : 0₃ ∈ c
    0∈c = there here

    0∈?c : 0₃ ∈? c
    0∈?c (there here) (there here) = refl
    0∈?c _ (there (there ()))
    0∈?c (there (there ())) _

    0∈!c : 0₃ ∈! c
    0∈!c = 0∈c , 0∈?c 0∈c

    1∈c-h : 1₃ ∈ c
    1∈c-h = here

    1∈c-t : 1₃ ∈ c
    1∈c-t = there (there here)

    2∉c : 2₃ ∉ c
    2∉c (there (there ()))

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 1∈c-h 1∈c-t of λ { () }

  module L222 where 
    c : ↺2
    c = 2₃ ∷ [ 2₃ ]

    2∈c : 2₃ ∈ c
    2∈c = here

    2∈c' : 2₃ ∈ c
    2∈c' = there here

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 2∈c 2∈c' of λ { () }

  module L2222 where 
    c : ↺2
    c = 2₃ ∷ 2₃ ∷ [ 2₃ ]

    2∈c : 2₃ ∈ c
    2∈c = here

    2∈c' : 2₃ ∈ c
    2∈c' = there here

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 2∈c 2∈c' of λ { () }

module Is0₃? where
  open M is0₃?

  module L00 where
    c : ↺0
    c = [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl

    0∈c : 0₃ ∈ c
    0∈c = here

    1∉c : 1₃ ∉ c
    1∉c ()

    2∉c : 2₃ ∉ c
    2∉c ()

  module C10 where
    c : 1↦*0
    c = 1₃ ∷ [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = there here

    1∈c : 1₃ ∈ c
    1∈c = here

    2∉c : 2₃ ∉ c
    2∉c (there ())

  module C01 where
    c : 0↦*1
    c = 0₃ ∷ [ 1₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = here

    1∈c : 1₃ ∈ c
    1∈c = there here

    2∉c : 2₃ ∉ c
    2∉c (there ())

  module L22 where
    c : ↺2
    c = [ 2₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl

    0∉c : 0₃ ∉ c
    0∉c ()

    1∉c : 1₃ ∉ c
    1∉c ()

    2∈c : 2₃ ∈ c
    2∈c = here

  module L010 where
    c : ↺0
    c = 0₃ ∷ 1₃ ∷ [ 0₃ ]

    0∈c-h : 0₃ ∈ c
    0∈c-h = here

    0∈c-t : 0₃ ∈ c
    0∈c-t = there (there here)

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 0∈c-h 0∈c-t of λ { () }

  module L101 where
    c : ↺1
    c = 1₃ ∷ 0₃ ∷ [ 1₃ ]

    0∈c : 0₃ ∈ c
    0∈c = there here

    0∈?c : 0₃ ∈? c
    0∈?c (there here) (there here) = refl
    0∈?c _ (there (there ()))
    0∈?c (there (there ())) _

    0∈!c : 0₃ ∈! c
    0∈!c = 0∈c , 0∈?c 0∈c

    1∈c-h : 1₃ ∈ c
    1∈c-h = here

    1∈c-t : 1₃ ∈ c
    1∈c-t = there (there here)

    2∉c : 2₃ ∉ c
    2∉c (there (there ()))

    c-no-chain : ¬(is-chain c)
    c-no-chain is = case is 1∈c-h 1∈c-t of λ { () }

  module C20 where
    c : 2↦*0
    c = 2₃ ∷ [ 0₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain here (there ())
    c-is-chain (there ()) here
    c-is-chain (there here) (there here) = refl

    0∈c : 0₃ ∈ c
    0∈c = there here

    1∉c : 1₃ ∉ c
    1∉c (there ())

    2∈c : 2₃ ∈ c
    2∈c = here

  module C201 where 
    c : 2↦*1
    c = 2₃ ∷ 0₃ ∷ [ 1₃ ]

    c-is-chain : is-chain c
    c-is-chain here here = refl
    c-is-chain (there p) (there q) = ap there (C01.c-is-chain p q)
    c-is-chain here (there (there ()))
    c-is-chain (there (there ())) here

    0∈c : 0₃ ∈ c
    0∈c = there here

    1∈c : 1₃ ∈ c
    1∈c = there (there here)

    2∈c : 2₃ ∈ c
    2∈c = here

    _∈c : ∀ x → x ∈ c
    0₃ ∈c = 0∈c
    1₃ ∈c = 1∈c
    2₃ ∈c = 2∈c

    _∈!c : ∀ x → x ∈! c
    x ∈!c = chain→⊆! c-is-chain (x ∈c)

    c-is-club : is-club c
    c-is-club = c-is-chain , 0∈c

module Gen (f : Fun) where
  open M f
-- -}
-- -}
-- -}
-- -}
-- -}
