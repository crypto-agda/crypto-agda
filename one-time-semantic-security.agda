module one-time-semantic-security where

open import Function
open import Data.Nat
open import flat-funs
open import Data.Vec using (splitAt)
open import program-distance
open import Data.Bits
open import flipbased-implem
open import Data.Product
open import Relation.Binary.PropositionalEquality

Coins = ℕ

-- module AbsSemSec (|M| |C| : ℕ) {FunPower : Set} {t} {T : Set t}
--                  (♭Funs : PoweredFlatFuns FunPower T) where
module AbsSemSec (|M| |C| : ℕ) {t} {T : Set t}
                 (♭Funs : FlatFuns T) where

  open FlatFuns ♭Funs

  M = `Bits |M|
  C = `Bits |C|

  record AbsSemSecAdv (|R| : Coins) : Set where
    constructor mk

    field
      {|S|} : ℕ

    S = `Bits |S|
    R = `Bits |R|

    field
      step₀ : R `→ (M `× M) `× S
      step₁ : C `× S `→ `Bit
      -- step₀ : ⟨ p₀ ⟩ R ↝ (M `× M) `× S
      -- step₁ : ⟨ p₁ ⟩ C `× S ↝ `Bit

  SemSecReduction : ∀ (f : Coins → Coins) → Set
  SemSecReduction f = ∀ {c} → AbsSemSecAdv c → AbsSemSecAdv (f c)

  -- runAdv is not the good name
  -- runAdv : ∀ {p} (A : AbsSemSecAdv p) → ⟨ ? ⟩ (C `× AbsSemSecAdv.R A) ↝ (M `× M) `× Bit
  -- runAdv (mk A-step₀ A-step₁) C = A-step₀ >>> id *** (const C &&& id >>> A-step₁)

{-
module FFF |M| |C| {♭Funs : FlatFuns ⊤ Set}
               (♭ops : FlatFunsOps _ ♭Funs)
               (run : ∀ {i o} → FlatFuns.⟨_⟩_↝_ ♭Funs _ i o → i → o) where
  open AbsSemSec |M| |C| ♭Funs
  module FunSemSecAdv {|R|} (A : AbsSemSecAdv |R|) where
    open AbsSemSecAdv A public
    open FlatFunsOps ♭ops
    step₀O : ⟨ _ ⟩ R ↝ ((⟨ _ ⟩ Bit ↝ M) × S)
    step₀O = {!run step₀!} >>> {!proj!} *** idO
-}

-- Here we use Agda functions for FlatFuns.
module FunSemSec (prgDist : PrgDist) (|M| |C| : ℕ) where
  open PrgDist prgDist
  open AbsSemSec |M| |C| fun♭Funs
  open FlatFunsOps fun♭Ops

  M² = Bit → M

  Enc : ∀ cc → Set
  Enc cc = M → ↺ cc C

  Tr : (cc₀ cc₁ : Coins) → Set
  Tr cc₀ cc₁ = Enc cc₀ → Enc cc₁

  FunSemSecAdv : Coins → Set
  -- FunSemSecAdv |R| = AbsSemSecAdv (mk _ _ |R|)
  FunSemSecAdv = AbsSemSecAdv

  module FunSemSecAdv {|R|} (A : FunSemSecAdv |R|) where
    open AbsSemSecAdv A public

    step₀F : R → (M² × S)
    step₀F = step₀ >>> proj *** idO

    step₀↺ : ↺ |R| (M² × S)
    step₀↺ = mk step₀F

    step₁F : S → C → Bit
    step₁F s c = step₁ (c , s)

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ {cc ca} (E : Enc cc) (A : FunSemSecAdv ca) b → ↺ (ca + cc) Bit
  runSemSec E A b
    = A-step₀ >>= λ { (m , s) → map↺ (A-step₁ s) (E (m b)) }
    where open FunSemSecAdv A renaming (step₀↺ to A-step₀; step₁F to A-step₁)

  _⇄_ : ∀ {cc ca} (E : Enc cc) (A : FunSemSecAdv ca) b → ↺ (ca + cc) Bit
  _⇄_ = runSemSec

  runAdv : ∀ {|R|} → FunSemSecAdv |R| → C → Bits |R| → (M × M) × Bit
  runAdv (mk A-step₀ A-step₁) C = A-step₀ >>> id *** (const C &&& id >>> A-step₁)

  _≗A_ : ∀ {p} (A₁ A₂ : FunSemSecAdv p) → Set
  A₀ ≗A A₁ = ∀ C R → runAdv A₀ C R ≡ runAdv A₁ C R

  change-adv : ∀ {cc ca} {E : Enc cc} {A₁ A₂ : FunSemSecAdv ca} → A₁ ≗A A₂ → (E ⇄ A₁) ≗⅁ (E ⇄ A₂)
  change-adv {ca = ca} {A₁ = _} {_} pf b R with splitAt ca R
  change-adv {E = E} {A₁} {A₂} pf b ._ | pre Σ., post , refl = trans (cong proj₂ (helper₀ A₁)) helper₂
     where open FunSemSecAdv
           helper₀ = λ A → pf (run↺ (E (proj (proj₁ (step₀ A pre)) b)) post) pre
           helper₂ = cong (λ m → step₁ A₂ (run↺ (E (proj (proj₁ m) b)) post , proj₂ (step₀ A₂ pre)))
                          (helper₀ A₂)

  module Unused (Power : Set) (coins : Power → Coins) where
  -- NP: not sure about these two. such a function has acess to the two encryption

    SemBroken : ∀ {cc} (E : Enc cc) → Power → Set
    SemBroken E power = ∃ (λ (A : FunSemSecAdv (coins power)) → breaks (E ⇄ A))

    -- functions.
    -- SemSecReduction p₀ p₁ E₀ E₁:
    --   security of E₀ reduces to security of E₁
    --   breaking E₁ reduces to breaking E₀
    SemSecReduction' : ∀ (p₀ p₁ : Power) {cc₀ cc₁} (E₀ : Enc cc₀) (E₁ : Enc cc₁) → Set
    SemSecReduction' p₀ p₁ E₀ E₁ = SemBroken E₁ p₁ → SemBroken E₀ p₀

  SafeSemSecReduction : ∀ (f : Coins → Coins) {cc₀ cc₁} (E₀ : Enc cc₀) (E₁ : Enc cc₁) → Set
  SafeSemSecReduction f E₀ E₁ =
     ∃ λ (red : SemSecReduction f) →
       ∀ {c} A → (E₀ ⇄ A) ⇓ (E₁ ⇄ red {c} A)

  SemSecTr : ∀ {cc₀ cc₁} (f : Coins → Coins) (tr : Tr cc₀ cc₁) → Set
  SemSecTr {cc₀} f tr = ∀ {E : Enc cc₀} → SafeSemSecReduction f (tr E) E

  -- SemSecReductionToOracle : ∀ (p₀ p₁ : Power) {cc} (E : Enc cc) → Set
  -- SemSecReductionToOracle = SemBroken E p₀ → Oracle p₁
