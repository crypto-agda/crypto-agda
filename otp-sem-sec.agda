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

module BitsExtra where
  splitAt′ : ∀ k {n} → Bits (k + n) → Bits k × Bits n
  splitAt′ k xs = case splitAt k xs of λ { (ys , zs , _) → (ys , zs) }

  vnot∘vnot : ∀ {n} → vnot {n} ∘ vnot ≗ id
  vnot∘vnot [] = refl
  vnot∘vnot (x ∷ xs) rewrite not-involutive x = cong (_∷_ x) (vnot∘vnot xs)

open BitsExtra

Coins = ℕ

module Guess (prgDist : PrgDist) where
  open PrgDist prgDist

  GuessAdv : Coins → Set
  GuessAdv c = ↺ c Bit

  runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ↺ ca Bit
  runGuess⅁ A _ = A

  -- An oracle: an adversary who can break the guessing game.
  Oracle : Coins → Set
  Oracle ca = ∃ (λ (A : GuessAdv ca) → breaks (runGuess⅁ A))

  -- Any adversary cannot do better than a random guess.
  GuessSec : Coins → Set
  GuessSec ca = ∀ (A : GuessAdv ca) → ¬(breaks (runGuess⅁ A))

module PostCompSec (prgDist : PrgDist) (|M| |C| : ℕ) where
  module PostCompRed {t} {T : Set t}
             {♭Funs : FlatFuns T}
             (♭ops : FlatFunsOps ♭Funs) where
    open FlatFunsOps ♭ops
    open AbsSemSec |M| |C| ♭Funs

    post-comp-red : (post-E : C `→ C) → SemSecReduction _
    post-comp-red post-E (mk A₀ A₁) = mk A₀ (post-E *** idO >>> A₁)

  open PrgDist prgDist
  open PostCompRed fun♭Ops
  open FlatFunsOps fun♭Ops
  open FunSemSec prgDist |M| |C|
  open AbsSemSec |M| |C| fun♭Funs

  post-comp : ∀ {cc} (post-E : C → C) → Tr cc cc
  post-comp post-E E = E >>> map↺ post-E

  post-comp-pres-sem-sec : ∀ {cc} (post-E : C → C)
                           → SemSecTr id (post-comp {cc} post-E)
  post-comp-pres-sem-sec post-E = post-comp-red post-E , (λ _ → id)

  post-comp-pres-sem-sec' : ∀ (post-E post-E⁻¹ : C → C)
                              (post-E-inv : post-E⁻¹ ∘ post-E ≗ id)
                              {cc} {E : Enc cc}
                            → SafeSemSecReduction id E (post-comp post-E E)
  post-comp-pres-sem-sec' post-E post-E⁻¹ post-E-inv {cc} {E} = red , helper where
    E' = post-comp post-E E
    red : SemSecReduction id
    red = post-comp-red post-E⁻¹
    helper : ∀ {p} A → (E ⇄ A) ⇓ (E' ⇄ red {p} A)
    helper {c} A A-breaks-E = A'-breaks-E'
     where open FunSemSecAdv A renaming (step₀F to A₀F)
           A' = red {c} A
           same-games : (E ⇄ A) ≗⅁ (E' ⇄ A')
           same-games b R
             rewrite post-E-inv (run↺ (E (proj₁ (A₀F (take c R)) b))
                                       (drop c R)) = refl
           A'-breaks-E' : breaks (E' ⇄ A')
           A'-breaks-E' = extensional-reduction same-games A-breaks-E

  post-neg : ∀ {cc} → Tr cc cc
  post-neg = post-comp vnot

  post-neg-pres-sem-sec : ∀ {cc} → SemSecTr id (post-neg {cc})
  post-neg-pres-sem-sec {cc} {E} = post-comp-pres-sem-sec vnot {E}

  post-neg-pres-sem-sec' : ∀ {cc} {E : Enc cc}
                            → SafeSemSecReduction id E (post-neg E)
  post-neg-pres-sem-sec' {cc} {E} = post-comp-pres-sem-sec' vnot vnot vnot∘vnot {cc} {E}

module Concrete k where
  open program-distance.Implem k
  module Guess' = Guess prgDist
  module FunSemSec' = FunSemSec prgDist
  module PostCompSec' = PostCompSec prgDist
