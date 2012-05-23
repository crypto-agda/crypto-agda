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

proj : ∀ {a} {A : Set a} → A × A → Bit → A
proj (x₀ , x₁) 0b = x₀
proj (x₀ , x₁) 1b = x₁

module BitsExtra where
  splitAt′ : ∀ k {n} → Bits (k + n) → Bits k × Bits n
  splitAt′ k xs = case splitAt k xs of λ { (ys , zs , _) → (ys , zs) }

  vnot∘vnot : ∀ {n} → vnot {n} ∘ vnot ≗ id
  vnot∘vnot [] = refl
  vnot∘vnot (x ∷ xs) rewrite not-involutive x = cong (_∷_ x) (vnot∘vnot xs)

open BitsExtra

Coins = ℕ

record PrgDist : Set₁ where
  constructor mk
  field
    _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
    ]-[-cong : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  _≗⅁_ : ∀ {c} (⅁₀ ⅁₁ : Bit → ↺ c Bit) → Set
  ⅁₀ ≗⅁ ⅁₁ = ∀ b → ⅁₀ b ≗↺ ⅁₁ b

  ≗⅁-trans : ∀ {c} → Transitive (_≗⅁_ {c})
  ≗⅁-trans p q b R = trans (p b R) (q b R)

  -- An wining adversary for game ⅁₀ reduces to a wining adversary for game ⅁₁
  _⇓_ : ∀ {c₀ c₁} (⅁₀ : Bit → ↺ c₀ Bit) (⅁₁ : Bit → ↺ c₁ Bit) → Set
  ⅁₀ ⇓ ⅁₁ = breaks ⅁₀ → breaks ⅁₁

  extensional-reduction : ∀ {c} {⅁₀ ⅁₁ : Bit → ↺ c Bit}
                          → ⅁₀ ≗⅁ ⅁₁ → ⅁₀ ⇓ ⅁₁
  extensional-reduction same-games = ]-[-cong (same-games 0b) (same-games 1b)

module Guess (Power : Set) (coins : Power → Coins) (prgDist : PrgDist) where
  open PrgDist prgDist

  GuessAdv : Coins → Set
  GuessAdv c = ↺ c Bit

  runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ↺ ca Bit
  runGuess⅁ A _ = A

  -- An oracle: an adversary who can break the guessing game.
  Oracle : Power → Set
  Oracle power = ∃ (λ (A : GuessAdv (coins power)) → breaks (runGuess⅁ A))

  -- Any adversary cannot do better than a random guess.
  GuessSec : Power → Set
  GuessSec power = ∀ (A : GuessAdv (coins power)) → ¬(breaks (runGuess⅁ A))

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

  SafeSemSecReduction : ∀ (f : Coins → Coins) {cc₀ cc₁} (E₀ : Enc cc₀) (E₁ : Enc cc₁) → Set
  SafeSemSecReduction f E₀ E₁ =
     ∃ λ (red : SemSecReduction f) →
       ∀ {c} A → (E₀ ⇄ A) ⇓ (E₁ ⇄ red {c} A)

  SemSecTr : ∀ {cc₀ cc₁} (f : Coins → Coins) (tr : Tr cc₀ cc₁) → Set
  SemSecTr {cc₀} f tr = ∀ {E : Enc cc₀} → SafeSemSecReduction f (tr E) E

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

open import diff
import Data.Fin as Fin
_]-_-[_ : ∀ {c} (f : ↺ c Bit) k (g : ↺ c Bit) → Set
_]-_-[_ {c} f k g = diff (Fin.toℕ #⟨ run↺ f ⟩) (Fin.toℕ #⟨ run↺ g ⟩) ≥ 2^(c ∸ k)
  --  diff (#1 f) (#1 g) ≥ 2^(-k) * 2^ c
  --  diff (#1 f) (#1 g) ≥ ε * 2^ c
  --  dist (#1 f) (#1 g) ≥ ε * 2^ c
  --    where ε = 2^ -k
  -- {!dist (#1 f / 2^ c) (#1 g / 2^ c) > ε !}

open import Data.Vec.NP using (count)

ext-count : ∀ {n a} {A : Set a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → count f xs ≡ count g xs
ext-count f≗g [] = refl
ext-count f≗g (x ∷ xs) rewrite ext-count f≗g xs | f≗g x = refl

ext-# : ∀ {c} {f g : Bits c → Bit} → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
ext-# f≗g = ext-count f≗g (allBits _)

]-[-cong : ∀ {k c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]- k -[ f' → g ]- k -[ g'
]-[-cong f≗g f'≗g' f]-[f' rewrite ext-# f≗g | ext-# f'≗g' = f]-[f'

module Concrete k where
  _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
  _]-[_ f g = f ]- k -[ g
  cong' : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'
  cong' = ]-[-cong {k}
  prgDist : PrgDist
  prgDist = mk _]-[_ cong'
  module Guess' = Guess Coins id prgDist
  module FunSemSec' = FunSemSec prgDist
  module PostCompSec' = PostCompSec prgDist
