{-# OPTIONS --without-K #-}
open import FFI.JS      using (JS!; _>>_)
open import FFI.JS.BigI using (BigI)
open import Algebra.Group.Homomorphism
import      Crypto.JS.BigI.CyclicGroup as 𝔾
import      Crypto.JS.BigI.FiniteField as 𝔽
open import Crypto.JS.BigI.Checks
open import Crypto.JS.BigI.ZqZp.Params using (Params; module Params)
open import Relation.Binary.PropositionalEquality

module Crypto.JS.BigI.ZqZp (params : Params) where

open Params params

checks! : JS!
checks! =
  check-pq-relation!      pI qI >>
  check-size! min-bits-q "q" qI >>
  check-size! min-bits-p "p" pI >>
  check-primality!       "q" qI primality-test-probability-bound >>
  check-primality!       "p" pI primality-test-probability-bound >>
  check-generator-group-order! gI qI pI

module ℤq = 𝔽 qI
  using (0#; 1#; _+_; _−_; _*_; +-grp) -- ; _/_)
  renaming ( 𝔽 to ℤq; BigI▹𝔽 to BigI▹ℤq; repr to ℤq-repr
           ; 𝔽-Eq? to ℤq-Eq?
           ; _⊗_ to _⊗I_ )
module ℤp★ = 𝔾 pI
  using (grp)
  renaming ( BigI▹𝔾 to BigI▹ℤp★; 𝔾 to ℤp★; _*_ to _·_
           ; _/_ to _·/_
           ; _^_ to _^I_
           ; 𝔾-Eq? to ℤp★-Eq?
           )

open ℤq  public
open ℤp★ public

g : ℤp★
g = BigI▹ℤp★ gI

_^_ : ℤp★ → ℤq → ℤp★
b ^ e = b ^I ℤq-repr e

⊗-spec : _*_ ≡ (λ x y → x ⊗I ℤq-repr y)
⊗-spec = refl

postulate
  ^-hom : ∀ b → GroupHomomorphism ℤq.+-grp ℤp★.grp  (_^_ b)
  *-hom : ∀ x → GroupHomomorphism ℤq.+-grp ℤq.+-grp (_*_ x)

-- -}
-- -}
-- -}
