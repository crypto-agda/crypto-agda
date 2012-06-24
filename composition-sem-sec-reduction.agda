module composition-sem-sec-reduction where

import Function as Fun
open Fun using (_∘_)
open import Data.Nat.NP using (ℕ)
open import Data.Bits using (vnot; vnot∘vnot≗id)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≗_)

open import flipbased-implem using (run↺; map↺)
open import program-distance using (module PrgDist; PrgDist)
open import flat-funs
open import one-time-semantic-security
import bit-guessing-game

-- One focuses on a particular kind of transformation
-- over a cipher, namely pre and post composing functions
-- to a given cipher E.
-- This transformation can change the size of input/output
-- of the given cipher.
module Comp (ep₀ : EncParams) (|M|₁ |C|₁ : ℕ) where
  open EncParams²-same-|R|ᵉ ep₀ |M|₁ |C|₁ using (M₀; M₁; C₀; C₁; Tr)
  open FlatFunsOps fun♭Ops using (_>>>_)

  comp : (pre-E : M₁ → M₀) (post-E : C₀ → C₁) → Tr
  comp pre-E post-E E = pre-E >>> E >>> map↺ post-E

-- This module shows how to adapt an adversary that is supposed to break
-- one time semantic security of some cipher E enhanced by pre and post
-- composition to an adversary breaking one time semantic security of the
-- original cipher E.
--
-- The adversary transformation works for any notion of function space
-- (FlatFuns) and the corresponding operations (FlatFunsOps).
-- Because of this abstraction the following construction can be safely
-- instantiated for at least three uses:
--   * When provided with a concrete notion of function like circuits
--     or at least functions over bit-vectors, one get a concrete circuit
--     transformation process.
--   * When provided with a high-level function space with real products
--     then proving properties about the code is made easy.
--   * When provided with a notion of cost such as time or space then
--     one get a the cost of the resulting adversary given the cost of
--     the inputs (adversary...).
module CompRed {t} {T : Set t}
               {♭Funs   : FlatFuns T}
               (♭ops    : FlatFunsOps ♭Funs)
               (ep₀ ep₁ : EncParams) where
  open FlatFuns ♭Funs
  open FlatFunsOps ♭ops
  open AbsSemSec ♭Funs
  open ♭EncParams² ♭Funs ep₀ ep₁ using (`M₀; `C₀; `M₁; `C₁)

  comp-red : (pre-E  : `M₁ `→ `M₀)
             (post-E : `C₀ `→ `C₁)
           → SemSecReduction ep₁ ep₀ _
  comp-red pre-E post-E (mk A₀ A₁) =
    mk (A₀ >>> first < pre-E × pre-E >) (first post-E >>> A₁)

module CompSec (prgDist : PrgDist) (ep₀ : EncParams) (|M|₁ |C|₁ : ℕ) where
  open PrgDist prgDist
  open FlatFunsOps fun♭Ops
  open FunSemSec prgDist
  open AbsSemSec fun♭Funs
  open EncParams²-same-|R|ᵉ ep₀ |M|₁ |C|₁
  open SemSecReductions ep₀ ep₁ id
  open CompRed fun♭Ops ep₀ ep₁

  private
    module Comp-implicit {x y z} = Comp x y z
  open Comp-implicit public

  comp-pres-sem-sec : ∀ pre-E post-E → SemSecTr (comp pre-E post-E)
  comp-pres-sem-sec pre-E post-E = comp-red pre-E post-E , λ E A → id

  comp-pres-sem-sec⁻¹ : ∀ pre-E pre-E⁻¹
                          (pre-E-right-inv : pre-E ∘ pre-E⁻¹ ≗ id)
                          post-E post-E⁻¹
                          (post-E-left-inv : post-E⁻¹ ∘ post-E ≗ id)
                        → SemSecTr⁻¹ (comp pre-E post-E)
  comp-pres-sem-sec⁻¹ pre-E pre-E⁻¹ pre-E-inv post-E post-E⁻¹ post-E-inv =
    SemSecTr→SemSecTr⁻¹
      (comp pre-E⁻¹ post-E⁻¹)
      (comp pre-E post-E)
      (λ E m R → ≡.trans (post-E-inv _)
      (≡.cong (λ x → run↺ (E x) R) (pre-E-inv _)))
      (comp-pres-sem-sec pre-E⁻¹ post-E⁻¹)

-- As a concrete example this module post-compose a negation of all the
-- bits.
module PostNegSec (prgDist : PrgDist) ep where
  open EncParams ep
  open EncParams² ep ep using (Tr)
  open CompSec prgDist ep |M| |C|
  open FunSemSec prgDist
  open Fun using (id)
  open SemSecReductions ep ep id

  post-neg : Tr
  post-neg = comp id vnot

  post-neg-pres-sem-sec : SemSecTr post-neg
  post-neg-pres-sem-sec = comp-pres-sem-sec id vnot

  post-neg-pres-sem-sec⁻¹ : SemSecTr⁻¹ post-neg
  post-neg-pres-sem-sec⁻¹ = comp-pres-sem-sec⁻¹ id id (λ _ → ≡.refl)
                                               vnot vnot vnot∘vnot≗id

-- Here we apply a concrete prgDist but still with an abstract precision
-- bound.
module ConcretePrgDist (k : ℕ) where
  open program-distance.Implem k
  module Guess-prgDist     = bit-guessing-game prgDist
  module FunSemSec-prgDist = FunSemSec prgDist
  module CompSec-prgDist   = CompSec prgDist
