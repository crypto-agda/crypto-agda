module otp-sem-sec where

import Level as L
open import Function
open import Data.Nat.NP
open import Data.Bits
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec hiding (_>>=_)
open import Data.Product.NP hiding (_⟦×⟧_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP
open import flipbased-implem
open ≡-Reasoning
open import Data.Unit using (⊤)
open import composable
open import vcomp
open import forkable
open import flat-funs
open import program-distance
open import one-time-semantic-security
import bit-guessing-game

module BitsExtra where
  splitAt′ : ∀ k {n} → Bits (k + n) → Bits k × Bits n
  splitAt′ k xs = case splitAt k xs of λ { (ys , zs , _) → (ys , zs) }

  vnot∘vnot : ∀ {n} → vnot {n} ∘ vnot ≗ id
  vnot∘vnot [] = refl
  vnot∘vnot (x ∷ xs) rewrite not-involutive x = cong (_∷_ x) (vnot∘vnot xs)

open BitsExtra







module CompRed {t} {T : Set t}
               {♭Funs : FlatFuns T}
               (♭ops : FlatFunsOps ♭Funs)
               (ep ep' : EncParams) where
    open FlatFunsOps ♭ops
    open AbsSemSec ♭Funs

    open EncParams ep using (|M|; |C|)
    open EncParams ep' using () renaming (|M| to |M|'; |C| to |C|')

    M = `Bits |M|
    C = `Bits |C|
    M' = `Bits |M|'
    C' = `Bits |C|'

    comp-red : (pre-E : M' `→ M)
               (post-E : C `→ C') → SemSecReduction ep' ep _
    comp-red pre-E post-E (mk A₀ A₁) = mk (A₀ >>> (pre-E *** pre-E) *** idO) (post-E *** idO >>> A₁)

module Comp (ep : EncParams) (|M|' |C|' : ℕ) where
  open EncParams ep

  ep' : EncParams
  ep' = EncParams.mk |M|' |C|' |R|e

  open EncParams ep' using () renaming (Enc to Enc'; M to M'; C to C')

  Tr = Enc → Enc'

  open FlatFunsOps fun♭Ops

  comp : (pre-E : M' → M) (post-E : C → C') → Tr
  comp pre-E post-E E = pre-E >>> E >>> {-weaken≤ |R|e≤|R|e' ∘-} map↺ post-E

module CompSec (prgDist : PrgDist) (ep : EncParams) (|M|' |C|' : ℕ) where
  open PrgDist prgDist
  open FlatFunsOps fun♭Ops
  open FunSemSec prgDist
  open AbsSemSec fun♭Funs

  open EncParams ep

  ep' : EncParams
  ep' = EncParams.mk |M|' |C|' |R|e

  open EncParams ep' using () renaming (Enc to Enc'; M to M'; C to C')

  module CompSec' (pre-E : M' → M) (post-E : C → C') where
    open SemSecReductions ep ep'
    open CompRed fun♭Ops ep ep' hiding (M; C)
    open Comp ep |M|' |C|'

    comp-pres-sem-sec : SemSecTr id (comp pre-E post-E)
    comp-pres-sem-sec = comp-red pre-E post-E , λ E A → id

  open SemSecReductions ep ep'
  open CompRed fun♭Ops ep ep' hiding (M; C)
  open CompSec' public
  module Comp' {x y z} = Comp x y z
  open Comp' hiding (Tr)
  comp-pres-sem-sec⁻¹ : ∀ pre-E pre-E⁻¹
                          (pre-E-right-inv : pre-E ∘ pre-E⁻¹ ≗ id)
                          post-E post-E⁻¹
                          (post-E-left-inv : post-E⁻¹ ∘ post-E ≗ id)
                        → SemSecTr⁻¹ id (comp pre-E post-E)
  comp-pres-sem-sec⁻¹ pre-E pre-E⁻¹ pre-E-inv post-E post-E⁻¹ post-E-inv =
    SemSecTr→SemSecTr⁻¹
      (comp pre-E⁻¹ post-E⁻¹)
      (comp pre-E post-E)
      (λ E m R → trans (post-E-inv _) (cong (λ x → run↺ (E x) R) (pre-E-inv _)))
      (comp-pres-sem-sec pre-E⁻¹ post-E⁻¹)

module PostNegSec (prgDist : PrgDist) ep where
  open EncParams ep
  open Comp ep |M| |C| hiding (Tr)
  open CompSec prgDist ep |M| |C|
  open FunSemSec prgDist
  open SemSecReductions ep ep

  post-neg : Tr
  post-neg = comp id vnot

  post-neg-pres-sem-sec : SemSecTr id post-neg
  post-neg-pres-sem-sec = comp-pres-sem-sec id vnot

  post-neg-pres-sem-sec⁻¹ : SemSecTr⁻¹ id post-neg
  post-neg-pres-sem-sec⁻¹ = comp-pres-sem-sec⁻¹ id id (λ _ → refl) vnot vnot vnot∘vnot

module Concrete k where
  open program-distance.Implem k
  module Guess' = bit-guessing-game prgDist
  module FunSemSec' = FunSemSec prgDist
  module CompSec' = CompSec prgDist
