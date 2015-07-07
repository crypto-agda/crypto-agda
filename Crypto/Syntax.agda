{-# OPTIONS --without-K #-}
open import Function.Base
import Data.String.Base as String
open import Algebra.Raw
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Field
open import Relation.Binary.PropositionalEquality.Base

module Crypto.Syntax where

record 𝕋 (U : Set) : Set where
  field
    Unit Bool String Number JSONValue ℤq ℤp★ : U
    Eff List                                 : U → U

module Types {U}(T : 𝕋 U)([_] : U → Set) where
  open 𝕋 T

  [_]! : U → Set
  [_]! = λ A → [ Eff A ]

  []! : Set
  []! = [ Unit ]!

  record Eq? {a} (A : U) : Set a where
    infix 7 _==_
    field
      _==_ : [ A ] → [ A ] → [ Bool ]
      {-
      ≡⇒== : ∀ {x y} → x ≡ y → ✓ (x == y)
      ==⇒≡ : ∀ {x y} → ✓ (x == y) → x ≡ y
      -}
--  open Eq? {{...}} public

record 𝕊 {U}(T : 𝕋 U)([_] : U → Set) : Set where
  open 𝕋 T
  open Types T [_] public

  infix 9 _^_

  field
    -- Bool
    false true :     [ Bool ]
    not        : Op₁ [ Bool ]
    _∧_ _∨_    : Op₂ [ Bool ]

    -- String
    «_»        : String.String → [ String ]
    _++_       : Op₂ [ String ]

    -- Number
    Number-read : [ String ] → [ Number ]!

    -- JSONValue
    _===_      : (x y : [ JSONValue ]) → [ Bool ]
    fromString : [ String ] → [ JSONValue ]
    toString   : [ JSONValue ] → [ String ]
    _·[_]      : [ JSONValue ] → [ JSONValue ] → [ JSONValue ]

    -- Eff
    return : ∀ {A} → [ A ] → [ A ]!
    _>>=_  : ∀ {A B} → [ A ]! → ([ A ] → [ B ]!) → [ B ]!
    assert : [ String ] → [ Bool ] → []!

    -- ℤq
    ℤq-read  : [ String ] → [ ℤq ]!
    ℤq-fld   : Field [ ℤq ]
    ℤq-Eq?   : Eq? ℤq
  --sum prod : [ List ℤq ] → [ ℤq ]

    -- ℤp★
    ℤp★-read : [ String ] → [ ℤp★ ]!
    ℤp★-grp  : Group [ ℤp★ ]
    ℤp★-Eq?  : Eq? ℤp★
  --prodp    : [ List ℤp★ ] → [ ℤp★ ]

    _^_    : [ ℤp★ ] → [ ℤq ] → [ ℤp★ ]
    ^-hom  : ∀ b → GroupHomomorphism (Field.+-grp ℤq-fld) ℤp★-grp (_^_ b)
    ^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x


  infixr 0  _>>_ _>>=_

  _>>_ : ∀ {A} → []! → [ A ]! → [ A ]!
  _>>_ = λ x y → x >>= λ _ → y

  module ℤq-Eq?  = Eq? ℤq-Eq?
  module ℤp★-Eq? = Eq? ℤp★-Eq?

  open module ℤq-fld  = Field ℤq-fld  public
    renaming (+-grp to ℤq+-grp)
    using (0#; 1#; _+_; _−_; 0−_; _*_; _/_)
  open module ℤp★-grp = Group ℤp★-grp public
    renaming (ε   to 1p
             ;_∙_ to _**_
             ;_⁻¹ to 1//_
             ;_/_ to _//_
             )
    using ()

  instance
    ℤq-Eq?'  = ℤq-Eq?
    ℤp★-Eq?' = ℤp★-Eq?

  _·«_»    : [ JSONValue ] → String.String → [ JSONValue ]
  x ·« y » = x ·[ fromString « y » ]

-- -}
-- -}
-- -}
-- -}
-- -}
